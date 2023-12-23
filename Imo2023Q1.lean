import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith

open PNat
open List
open LT

def natLe (a b : ℕ) : Prop := a ≤ b

def natLtplusone (n : ℕ) : (n < n + 1 ) := by
simp

-- Instances for `natLe` to be used with `Finset.sort`.
instance : DecidableRel natLe := fun a b => inferInstanceAs (Decidable (a ≤ b))
instance : IsTrans ℕ natLe := ⟨fun _ _ _ => Nat.le_trans⟩
instance : IsAntisymm ℕ natLe := ⟨fun _ _ => Nat.le_antisymm⟩
instance : IsTotal ℕ natLe := ⟨fun a b => Nat.le_total a b⟩

-- Sort the divisors using the `natLe` relation.
def sorted_divisors (n : ℕ) : List ℕ :=
  let divs : Finset ℕ := Nat.divisors n
  Finset.sort natLe divs

def has_divisibility_property (n : ℕ) (h : length (sorted_divisors n) > 0) : Prop :=
  let divs_sorted := sorted_divisors n
  ∀ i : Fin (length divs_sorted - 2),
    have h0 : i < (length divs_sorted - 2) := i.isLt
    have h1 : i < length divs_sorted := lt.trans (Nat.lt_succ_self i.val) (by omega)
    let di := divs_sorted.get ⟨i.val, by omega⟩
    let di1 := divs_sorted.get ⟨i.val + 1, by omega⟩
    let di2 := divs_sorted.get ⟨i.val + 2, by omega⟩
    di ∣ (di1 + di2)
