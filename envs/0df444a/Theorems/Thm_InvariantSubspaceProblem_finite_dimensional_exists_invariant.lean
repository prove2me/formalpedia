-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_finite_dimensional_exists_invariant
-- name    : InvariantSubspaceProblem.finite_dimensional_exists_invariant
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T17:20:37.875964+00:00
-- url     : https://prove2.me/theorems/6d62badb-efb0-4282-b822-a23ac72aaa33
-- title:
--   Operators on finite-dimensional complex spaces have invariant subspaces
-- statement:
--   Let $E$ be a finite-dimensional complex normed space with $\dim_{\mathbb{C}} E\ge 2$, and let $T\colon E\to E$ be a linear operator. Then $T$ has a non-trivial closed invariant subspace: there is a closed subspace $S$ with $\{0\}\neq S\neq E$ and $T(S)\subseteq S$.
--
--   This is the reason the invariant subspace problem is only posed in infinite dimensions (an eigenvector of $T$ spans such a subspace).
--
--   **Formalization Note** In finite dimensions every subspace is closed and every linear map is bounded, so the statement is the purely algebraic fact.
-- source:
--   Open Problem Garden, 'Invariant subspace problem' (posted by tchow, 9 Feb 2009), http://www.openproblemgarden.org/op/invariant_subspace_problem (the problem is restricted to infinite-dimensional spaces); Radjavi & Rosenthal, Invariant Subspaces, Springer 1973.

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem finite_dimensional_exists_invariant (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (hdim : 2 ≤ Module.finrank ℂ E)
    (T : E →L[ℂ] E) : HasNontrivialClosedInvariantSubspace T := by sorry

end InvariantSubspaceProblem
