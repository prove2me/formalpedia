-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_argyros_haydon_invariant_subspace
-- name    : InvariantSubspaceProblem.argyros_haydon_invariant_subspace
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T17:27:12.060724+00:00
-- url     : https://prove2.me/theorems/8cd45bc6-3218-4619-99b2-02a29c1e319f
-- title:
--   Argyros–Haydon: a space where the invariant subspace problem has a positive answer
-- statement:
--   **Theorem (Argyros–Haydon 2011).** There exists a separable, infinite-dimensional real Banach space $E$ such that every bounded linear operator $T\colon E\to E$ has a non-trivial closed invariant subspace.
--
--   This is the statement quoted by the source: "Argyros and Haydon constructed a Banach space for which the corresponding question has a positive answer". It follows from the scalar-plus-compact property together with the Aronszajn–Smith theorem.
-- source:
--   S. A. Argyros & R. G. Haydon, A hereditarily indecomposable L∞-space that solves the scalar-plus-compact problem, Acta Math. 206 (2011) 1–54, arXiv:0903.3921 ; as quoted in Open Problem Garden, 'Invariant subspace problem' (posted by tchow, 9 Feb 2009), http://www.openproblemgarden.org/op/invariant_subspace_problem, reference [4].

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem argyros_haydon_invariant_subspace :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E) (_ : CompleteSpace E),
      TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional ℝ E ∧
      ∀ T : E →L[ℝ] E, HasNontrivialClosedInvariantSubspace T := by sorry

end InvariantSubspaceProblem
