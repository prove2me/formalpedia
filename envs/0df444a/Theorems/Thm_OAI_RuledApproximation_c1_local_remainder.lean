-- Prove2me | Theorems.Thm_OAI_RuledApproximation_c1_local_remainder
-- name    : OAI.RuledApproximation.c1_local_remainder
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:46:30.732071+00:00
-- url     : https://prove2.me/theorems/ea0268ab-a7c7-4ddf-9eda-e904902d4e42
-- title:
--   Uniform first-order remainder bound for a $C^1$ map near a point
-- statement:
--   Let $E$ and $F$ be real normed spaces, let $U\subseteq E$ be open, and let $v:E\to F$ be continuously differentiable ($C^1$) on $U$. Let $p\in U$ and $\delta>0$. Then there is a radius $r>0$ such that the open ball $B(p,r)$ is contained in $U$ and
--   $$
--   \|v(x)-v(y)-Dv(p)(x-y)\|\le\delta\,\|x-y\|\qquad\text{for all } x,y\in B(p,r),
--   $$
--   where $Dv(p):E\to F$ is the Fréchet derivative of $v$ at $p$.
--
--   This is a quantitative form of strict differentiability: near $p$ the map $v$ differs from its linearization at $p$ by a $\delta$-Lipschitz map. In the covering construction it supplies, for an arbitrarily small $\delta$, the remainder hypothesis $\|w(x)-w(y)-A(x-y)\|\le\delta\|x-y\|$ on a patch, where $A$ is the derivative at the centre of the patch.
--
--   **Formalization Note** The hypothesis is `ContDiffOn ℝ 1 v U`, the derivative is `fderiv ℝ v p`, and `ball p r` is the open ball.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/LocalApproximation.lean#L13-L31

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.c1_local_remainder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : E → F} {U : Set E} (hU : IsOpen U) (hv : ContDiffOn ℝ 1 v U)
    {p : E} (hp : p ∈ U) {delta : ℝ} (hd : 0 < delta) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
      ‖v x - v y - fderiv ℝ v p (x - y)‖ ≤ delta * ‖x - y‖ := by sorry
