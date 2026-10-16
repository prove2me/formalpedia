-- Prove2me | Theorems.Thm_OAI_ThreeManifold_PassageDynamics_scalar_reflection_germ
-- name    : OAI.ThreeManifold.PassageDynamics.scalar_reflection_germ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:27:50.725121+00:00
-- url     : https://prove2.me/theorems/bb1d1b03-b4c4-4728-b01f-7ba274e84184
-- title:
--   Solutions of $t''=-\tfrac12F(t)$ are locally time-symmetric about a turning point
-- statement:
--   Let $F:\mathbb{R}\to\mathbb{R}$ be $C^\infty$, let $U\subseteq\mathbb{R}$ be open and $c\in U$. Let $t,v:\mathbb{R}\to\mathbb{R}$ be functions such that for every $s\in U$, $t$ is differentiable at $s$ with $t'(s)=v(s)$ and $v$ is differentiable at $s$ with $v'(s)=-\tfrac12F(t(s))$. Assume the velocity vanishes at $c$, $v(c)=0$. Then there is a neighbourhood of $c$ on which
--   $$
--   t(2c-s)=t(s)\qquad\text{and}\qquad -v(2c-s)=v(s).
--   $$
--
--   In words: a solution of the conservative equation $t''=-\tfrac12F(t)$ is, near any turning point $c$ (a zero of the velocity), symmetric under the time reflection $s\mapsto 2c-s$, with $t$ even and $v$ odd about $c$. This germ-level statement is what makes the even/odd reflection of a solution about a turning point smooth at the turning point itself.
--
--   **Formalization Note** The conclusion is stated as equality of functions eventually in the neighbourhood filter of $c$ (`=ᶠ[nhds c]`); derivatives are two-sided (`HasDerivAt`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Passages.lean#L748-L767

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages

open OAI OAI.ThreeManifold OAI.ThreeManifold.PassageDynamics
open Set Filter Topology
open scoped ContDiff

theorem OAI.ThreeManifold.PassageDynamics.scalar_reflection_germ {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) {c : ℝ} (hc : c ∈ U)
    (ht : ∀ s ∈ U, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ U, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0) :
    (fun s => t (2*c-s)) =ᶠ[nhds c] t ∧ (fun s => -v (2*c-s)) =ᶠ[nhds c] v := by sorry
