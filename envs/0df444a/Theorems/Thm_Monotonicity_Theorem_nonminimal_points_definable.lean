-- Prove2me | Theorems.Thm_Monotonicity_Theorem_nonminimal_points_definable
-- name    : Monotonicity_Theorem.nonminimal_points_definable
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:27:39.404837+00:00
-- url     : https://prove2.me/theorems/2454f132-4c48-469c-afe6-fa478a7d2774
-- title:
--   Non-minimal points of a definable function are definable
-- statement:
--   The set of domain points admitting a strictly smaller point with the same function value is definable. The joint relation is built by reindexing the graph and order into a three-coordinate space and projecting, so fiber minima become definable by complementation. This is the core of the Lemma 1 finite-fiber case.
-- source:
--   monotonicity.tex, Lemma 1 finite-fiber step; supporting definability lemma

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.nonminimal_points_definable {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (fun x : Power R 1 => exists w : Power R 1, I w /\ Lt1 D w x /\
      exists hxw : I w, exists hxx : I x,
        (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk x hxx)).1) := by sorry
