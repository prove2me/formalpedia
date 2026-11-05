-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Taylor_linearCauchy_height_initial_state
-- name    : OAI.SmoothLocal.Taylor.linearCauchy_height_initial_state
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:24.906215+00:00
-- url     : https://prove2.me/theorems/ba83cd87-8f3a-4229-b290-0496cbe19d44
-- title:
--   Linear Cauchy polynomial has the height jet on the initial cut
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $z$ be smooth on an open set $U$ containing the horizontal segment $\{(x,a):x\in(\ell,r)\}$. Put $u_0(x)=z(x,a)$, $u_1(x)=\partial_yz(x,a)$ and $P(x,y)=u_0(x)+u_1(x)(y-a)$. Then for every $x\in(\ell,r)$ the six-variable jets agree:
--
--   $$\big(x,a,P_x,P_y,P_{xy},P_{xx}\big)(x,a)=\big(x,a,z_x,z_y,z_{xy},z_{xx}\big)(x,a).$$
--
--   This says that the degree-one time polynomial built from the Cauchy data of $z$ on the cut $y=a$ reproduces every argument of the Darboux right-hand side at that cut. It is the base case of the Taylor comparison across the thin strip.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Taylor.linearCauchy_height_initial_state` in `lean/OAI/Geometry/IsometricImmersion/Taylor/TaylorCauchyData.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Taylor/TaylorCauchyData.lean; Section 4.3

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Weighted

theorem linearCauchy_height_initial_state {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (left right a : ℝ)
    (hcut : ∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ U)
    {x : ℝ} (hx : x ∈ Ioo left right) :
    qSolutionJet (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a)) ![x, a] =
      qSolutionJet z ![x, a] := by
  sorry

end SmoothLocal.Taylor
end
end OAI
