-- Prove2me | Theorems.Thm_Monotonicity_Theorem_fiber_minimals_definable
-- name    : Monotonicity_Theorem.fiber_minimals_definable
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T17:45:45.044692+00:00
-- url     : https://prove2.me/theorems/cb089af4-8398-482e-886a-f01077c81c71
-- title:
--   Definability of fiber-minimal points
-- statement:
--   The set of fiber-minimal domain points is definable: points with no strictly smaller point sharing their function value. This is the domain intersected with the complement of the non-minimal set, and it carries the minimum-preimage construction of the Lemma 1 finite-fiber case.
-- source:
--   monotonicity.tex, Lemma 1 finite-fiber step; supporting definability lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.fiber_minimals_definable {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (fun x : Power R 1 => I x /\ ¬ exists w : Power R 1, I w /\ Lt1 D w x /\
      exists hxw : I w, exists hxx : I x,
        (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk x hxx)).1) := by sorry
