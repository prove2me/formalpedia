-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_lambdaFree_add_span_recCone
-- name    : MaxLatticeFree.Geometry.lambdaFree_add_span_recCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:16:16.357997+00:00
-- url     : https://prove2.me/theorems/4ad2c2de-9d03-4d11-b0f1-81faba59ab0e
-- title:
--   Lemma 16 — adding the span of the recession cone preserves $\Lambda$-freeness
-- statement:
--   Let $\Lambda$ be a lattice of a linear space $V\subseteq\mathbb R^n$, let $S$ be a $\Lambda$-free convex set of $V$, and let $C=\operatorname{rec}(S)$ be its recession cone. Then the Minkowski sum
--
--   $$
--   S+\langle C\rangle=\{\,s+c \mid s\in S,\ c\in\langle C\rangle\,\}
--   $$
--
--   is again a $\Lambda$-free convex set of $V$, where $\langle C\rangle$ is the linear span of $C$.
--
--   Consequently a maximal $\Lambda$-free convex set of $V$ equals $S+\langle C\rangle$, so its recession cone is a linear space.
--
--   **Formalization Note** "$\Lambda$-free" carries no explicit ambient space on the page; by the standing assumption of §2.2 it is relative to $V$.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 12, Lemma 16

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_recCone

open Pointwise

namespace MaxLatticeFree.Geometry

theorem lambdaFree_add_span_recCone {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsLambdaFree Λ V S) :
    IsLambdaFree Λ V (S + (Submodule.span ℝ (recCone S) : Set (EuclideanSpace ℝ (Fin n)))) := by sorry

end MaxLatticeFree.Geometry
