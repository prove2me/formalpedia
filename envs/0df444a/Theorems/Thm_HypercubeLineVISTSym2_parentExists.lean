-- Prove2me | Theorems.Thm_HypercubeLineVISTSym2_parentExists
-- name    : HypercubeLineVISTSym2_parentExists
-- status  : Proved
-- author  : @undercat
-- created : 2026-09-27T15:58:10.661261+00:00
-- url     : https://prove2.me/theorems/9c68e90f-5dcf-423d-994b-51e002b5cff5
-- title:
--   Existence of Sym2 parent family with VIST properties
-- statement:
--   There exists a family of 2n-2 parent functions on Sym2 with the rooted tree, independence, and distinct-children properties.

import Mathlib.Data.Sym.Sym2

theorem HypercubeLineVISTSym2_parentExists (n : Nat) (hn : 3 < n) :
    ∀ (rSym2 : Sym2 (Fin n → Bool)) (a b : Fin n → Bool) (d0 : Fin n),
      rSym2 = Sym2.mk a b →
      ∃ parentSym2 : Fin (2 * n - 2) → Sym2 (Fin n → Bool) → Sym2 (Fin n → Bool),
        (∀ k : Fin (2 * n - 2), parentSym2 k rSym2 = rSym2) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool), v ≠ rSym2 →
          ∃ x y1 y2 : Fin n → Bool, v = Sym2.mk x y1 ∧ parentSym2 k v = Sym2.mk x y2) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool),
          ∃ m : Nat, (parentSym2 k)^[m] v = rSym2) ∧
        (∀ k l : Fin (2 * n - 2), k ≠ l →
          ∀ v u : Sym2 (Fin n → Bool),
            (∃ mk : Nat, (parentSym2 k)^[mk] v = u) →
            (∃ ml : Nat, (parentSym2 l)^[ml] v = u) →
            u = rSym2 ∨ u = v) ∧
        (∀ k l : Fin (2 * n - 2), k ≠ l →
          ∀ v : Sym2 (Fin n → Bool), v ≠ rSym2 →
            parentSym2 k v = rSym2 → parentSym2 l v ≠ rSym2) := by
  sorry
