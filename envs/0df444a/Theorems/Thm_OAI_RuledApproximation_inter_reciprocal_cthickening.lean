-- Prove2me | Theorems.Thm_OAI_RuledApproximation_inter_reciprocal_cthickening
-- name    : OAI.RuledApproximation.inter_reciprocal_cthickening
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:42:41.894426+00:00
-- url     : https://prove2.me/theorems/619d5d51-589a-460e-ba5d-2477b11cba9b
-- title:
--   A closed set is the intersection of its closed $\tfrac{1}{n+1}$-neighbourhoods
-- statement:
--   Let $(E,d)$ be a metric space and let $K\subseteq E$ be closed. For $\delta\ge0$ let $\overline N_\delta(K)=\{x\in E:\ \operatorname{dist}(x,K)\le\delta\}$ be the closed $\delta$-neighbourhood of $K$, where $\operatorname{dist}(x,K)=\inf_{y\in K}d(x,y)$ (equal to $+\infty$ when $K$ is empty). Then
--   $$
--   \bigcap_{n=0}^{\infty}\overline N_{1/(n+1)}(K)=K.
--   $$
--
--   The neighbourhoods $\overline N_{1/(n+1)}(K)$ decrease in $n$, so this exhibits $K$ as the limit of a decreasing sequence of closed neighbourhoods. Combined with continuity of integrals along decreasing sequences of sets, it shows that integrals over these neighbourhoods converge to the integral over $K$, with no assumption on the boundary of $K$ (which may have positive measure).
--
--   **Formalization Note** The neighbourhoods are Mathlib's `cthickening (1 / (n + 1)) K`, defined through the extended-real infimum distance `infEDist`, and $n$ ranges over $\mathbb{N}=\{0,1,2,\dots\}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/OuterApproximation.lean#L12-L26

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.inter_reciprocal_cthickening {E : Type*} [MetricSpace E] (K : Set E)
    (hK : IsClosed K) :
    (⋂ n : ℕ, cthickening (1 / ((n : ℝ) + 1)) K) = K := by sorry
