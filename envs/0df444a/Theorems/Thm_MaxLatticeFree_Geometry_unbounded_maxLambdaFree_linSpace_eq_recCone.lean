-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_unbounded_maxLambdaFree_linSpace_eq_recCone
-- name    : MaxLatticeFree.Geometry.unbounded_maxLambdaFree_linSpace_eq_recCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:19:15.505773+00:00
-- url     : https://prove2.me/theorems/b3f57dbc-acb6-44d9-ab9a-915ce5d81a2c
-- title:
--   Claim 1 in the proof of Theorem 10 — lineality space equals recession cone
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$ and let $S$ be a maximal $\Lambda$-free convex set of $V$ with $\dim(S)=\dim(V)$ that is unbounded. Let $C$ be the recession cone of $S$ and $L$ its lineality space. Then
--
--   $$
--   L=C .
--   $$
--
--   So the recession cone of such a set is a linear space and $S$ is a cylinder $S=P+L$ over a bounded set $P$.
--
--   **Formalization Note** The hypotheses are the standing context of Claim 1 on pp. 13–14 (maximality, full dimension, unboundedness). The equality is between sets of directions (`linSpace S = recCone S`).
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 14, Claim 1 in the proof of Theorem 10

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_recCone
import Definitions.Def_MaxLatticeFree_Geometry_affDim

namespace MaxLatticeFree.Geometry

theorem unbounded_maxLambdaFree_linSpace_eq_recCone {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsMaxLambdaFree Λ V S)
    (hdim : affDim S = (Module.finrank ℝ V : ℤ)) (hunbdd : ¬ Bornology.IsBounded S) :
    linSpace S = recCone S := by sorry

end MaxLatticeFree.Geometry
