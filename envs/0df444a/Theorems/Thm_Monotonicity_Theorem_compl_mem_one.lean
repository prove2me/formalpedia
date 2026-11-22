-- Prove2me | Theorems.Thm_Monotonicity_Theorem_compl_mem_one
-- name    : Monotonicity_Theorem.compl_mem_one
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:28:17.880398+00:00
-- url     : https://prove2.me/theorems/a3b2ad9e-9506-4f7b-a62b-4e87d23266ff
-- title:
--   Complements of one-dimensional definable sets are definable
-- statement:
--   The complement of a one-dimensional definable set is definable. On the line this follows from o-minimality: a finite union of points and intervals has a complement of the same shape. This supplies the missing complement operation used to carve out fiber-minimal points in the Lemma 1 finite-fiber case.
-- source:
--   monotonicity.tex, Lemma 1 finite-fiber step; supporting definability lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.compl_mem_one {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {A : Set (Power R 1)}
    (hA : M.S 1 A) :
    M.S 1 (fun x : Power R 1 => ¬ A x) := by sorry
