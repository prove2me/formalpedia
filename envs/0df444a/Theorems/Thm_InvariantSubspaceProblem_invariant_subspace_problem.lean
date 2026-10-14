-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_invariant_subspace_problem
-- name    : InvariantSubspaceProblem.invariant_subspace_problem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T17:27:39.193928+00:00
-- url     : https://prove2.me/theorems/2f280041-16aa-484e-9c89-f067f43c8daa
-- title:
--   Invariant subspace problem (Hilbert space)
-- statement:
--   **Invariant subspace problem.** Let $H$ be an infinite-dimensional, separable, complex Hilbert space and let $T\colon H\to H$ be a bounded linear operator. Then there is a closed linear subspace $S\subseteq H$ such that
--
--   $$
--   \{0\}\neq S\neq H \qquad\text{and}\qquad T(S)\subseteq S .
--   $$
--
--   The source asks this as a yes/no question ("Does every bounded linear operator on an infinite-dimensional separable Hilbert space have a non-trivial closed invariant subspace?"); this item states the affirmative answer. A proof of the statement or a proof of its negation both settle the problem. It is one of the most famous open problems in functional analysis.
--
--   **Formalization Note** Complex scalars are used, as is standard for this problem. Separability is assumed because on non-separable spaces the answer is easily positive; infinite dimension is assumed because the finite-dimensional case is elementary. The zero operator is not excluded (it trivially satisfies the conclusion).
-- source:
--   Open Problem Garden, 'Invariant subspace problem' (posted by tchow, 9 Feb 2009), http://www.openproblemgarden.org/op/invariant_subspace_problem (problem statement).

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem invariant_subspace_problem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (hinf : ¬ FiniteDimensional ℂ H)
    (T : H →L[ℂ] H) : HasNontrivialClosedInvariantSubspace T := by sorry

end InvariantSubspaceProblem
