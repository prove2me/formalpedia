-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_normal_exists_invariant
-- name    : InvariantSubspaceProblem.normal_exists_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T17:22:33.297284+00:00
-- url     : https://prove2.me/theorems/0b135efa-094b-4039-b09f-5334046842e1
-- title:
--   Normal operators have closed invariant subspaces
-- statement:
--   Let $H$ be a complex Hilbert space of dimension at least $2$ and let $T\colon H\to H$ be a bounded **normal** operator, i.e. $T^*T=TT^*$. Then $T$ has a non-trivial closed invariant subspace.
--
--   This is a classical consequence of the spectral theorem for normal operators and is one of the standard positive partial results on the invariant subspace problem.
--
--   **Formalization Note** Normality is Mathlib's `IsStarNormal` for the C*-algebra of bounded operators on $H$; the dimension hypothesis is $\operatorname{rank}_{\mathbb{C}} H>1$ (cardinal-valued, so infinite dimension is included). Separability is not assumed.
-- source:
--   Radjavi & Rosenthal, Invariant Subspaces, Springer 1973 (normal operators); Open Problem Garden, 'Invariant subspace problem' (posted by tchow, 9 Feb 2009), http://www.openproblemgarden.org/op/invariant_subspace_problem, overview references [2],[3],[5].

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem normal_exists_invariant (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hdim : 1 < Module.rank ℂ H) (T : H →L[ℂ] H) [IsStarNormal T] :
    HasNontrivialClosedInvariantSubspace T := by sorry

end InvariantSubspaceProblem
