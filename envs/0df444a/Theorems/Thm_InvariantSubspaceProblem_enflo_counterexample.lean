-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_enflo_counterexample
-- name    : InvariantSubspaceProblem.enflo_counterexample
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T17:25:31.904408+00:00
-- url     : https://prove2.me/theorems/b1545b0b-ec15-4966-8804-0dd86a5f84c1
-- title:
--   Enflo: a Banach-space operator without closed invariant subspaces
-- statement:
--   **Theorem (Enflo 1987).** There exist a separable, infinite-dimensional complex Banach space $E$ and a bounded linear operator $T\colon E\to E$ that has **no** non-trivial closed invariant subspace.
--
--   This is the negative answer to the Banach-space version of the problem, cited as reference [1] of the source. It shows that any positive solution in Hilbert space must use the Hilbert-space structure.
--
--   **Formalization Note** The space is existentially quantified (in `Type`), together with its normed-space structure.
-- source:
--   P. Enflo, On the invariant subspace problem for Banach spaces, Acta Math. 158 (1987) 213–313, https://doi.org/10.1007/BF02392260 , main theorem; cited as [1] in Open Problem Garden, 'Invariant subspace problem' (posted by tchow, 9 Feb 2009), http://www.openproblemgarden.org/op/invariant_subspace_problem.

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem enflo_counterexample :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E) (_ : CompleteSpace E),
      TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional ℂ E ∧
      ∃ T : E →L[ℂ] E, ¬ HasNontrivialClosedInvariantSubspace T := by sorry

end InvariantSubspaceProblem
