-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_unbounded_maxLambdaFree_linSpace_isLambdaSubspace
-- name    : MaxLatticeFree.Geometry.unbounded_maxLambdaFree_linSpace_isLambdaSubspace
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:20:01.041692+00:00
-- url     : https://prove2.me/theorems/a8a3999f-4381-43b2-9755-15c17910adca
-- title:
--   Claim 2 in the proof of Theorem 10 — the lineality space is a $\Lambda$-subspace
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$ and let $S$ be a maximal $\Lambda$-free convex set of $V$ with $\dim(S)=\dim(V)$ that is unbounded. Let $L$ be the lineality space of $S$. Then
--
--   $$
--   L \text{ is a linear subspace of } V \text{ and a } \Lambda\text{-subspace of } V .
--   $$
--
--   Together with Lemma 17 this lets the proof of Theorem 10 project $S=P+L$ onto $L^\perp\cap V$, where $P$ is a bounded maximal lattice-free set for a lattice, and apply Lemma 13.
--
--   **Formalization Note** The hypotheses are the standing context of Claim 2 on pp. 13–14. The conclusion states that the set of lineality directions is (the carrier of) a submodule that is a $\Lambda$-subspace.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 14, Claim 2 in the proof of Theorem 10

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_recCone
import Definitions.Def_MaxLatticeFree_Geometry_affDim

namespace MaxLatticeFree.Geometry

theorem unbounded_maxLambdaFree_linSpace_isLambdaSubspace {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsMaxLambdaFree Λ V S)
    (hdim : affDim S = (Module.finrank ℝ V : ℤ)) (hunbdd : ¬ Bornology.IsBounded S) :
    ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), (L : Set (EuclideanSpace ℝ (Fin n))) = linSpace S ∧ IsLambdaSubspace Λ V L := by sorry

end MaxLatticeFree.Geometry
