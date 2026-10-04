-- Prove2me | Theorems.Thm_HypercubeLineVISTSym2_parentExistsStrong
-- name    : HypercubeLineVISTSym2_parentExistsStrong
-- status  : Proved
-- author  : @undercat
-- created : 2026-09-27T15:58:34.425858+00:00
-- url     : https://prove2.me/theorems/bc0747b8-f27a-4018-a53b-78c6f1fceb9f
-- title:
--   Existence of Sym2 parent family (strong version)
-- statement:
--   Strong existence of Sym2 parent family preserving valid edges.

import Mathlib.Data.Sym.Sym2

theorem HypercubeLineVISTSym2_parentExistsStrong (n : Nat) (hn : 3 < n) :
    ∀ (rSym2 : Sym2 (Fin n → Bool)) (a b : Fin n → Bool) (d0 : Fin n),
      rSym2 = Sym2.mk a b →
      (∃ c0 : Fin n, (∀ j : Fin n, j ≠ c0 → a j = b j) ∧ a c0 ≠ b c0) →
      ∃ parentSym2 : Fin (2 * n - 2) → Sym2 (Fin n → Bool) → Sym2 (Fin n → Bool),
        (∀ k : Fin (2 * n - 2), parentSym2 k rSym2 = rSym2) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool),
          (∃ x y c : Fin n → Bool, ∃ cc : Fin n,
            v = Sym2.mk x y ∧ (∀ j : Fin n, j ≠ cc → x j = y j) ∧ x cc ≠ y cc) →
          (∃ x y c : Fin n → Bool, ∃ cc : Fin n,
            parentSym2 k v = Sym2.mk x y ∧ (∀ j : Fin n, j ≠ cc → x j = y j) ∧ x cc ≠ y cc)) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool), v ≠ rSym2 →
          ∃ x y1 y2 : Fin n → Bool, v = Sym2.mk x y1 ∧ parentSym2 k v = Sym2.mk x y2) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool),
          ∃ m : Nat, (parentSym2 k)^[m] v = rSym2) := by
  sorry
