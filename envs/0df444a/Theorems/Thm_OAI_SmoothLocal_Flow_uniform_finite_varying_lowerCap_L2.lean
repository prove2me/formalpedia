-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Flow_uniform_finite_varying_lowerCap_L2
-- name    : OAI.SmoothLocal.Flow.uniform_finite_varying_lowerCap_L2
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:42.01025+00:00
-- url     : https://prove2.me/theorems/744dd720-068f-46b4-9a5d-de5d4e2b1359
-- title:
--   Uniform $L^2$ bounds of all orders on lower-cap rectangles for a varying metric
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Fix $G,Z\ge0$, $d,c>0$, $e_0,\kappa$ and a budget $J$ prescribing metric jet bounds on lower-cap rectangles. For every $k$ and every lower-cap rectangle $r$, provided the budget values requested by the induction are nonnegative, there is $H\ge0$ such that the following holds for all $g$, $U$, $z$, $Y$, $W$. If $g$ is smooth and positive on an open $U\supseteq S$ with $C^4$ bound $G$ and $|\det g|\ge d$ on $S$, $z$ is a cap-induction height and $Y$ its cap-induction flow, and $g$ satisfies the requested finite jet bounds on the rectangles requested, then
--
--   $$\sum_{|\alpha|\le k+8}\text{each }\|\partial^\alpha z\|_{L^2(\Phi(r))}\le H.$$
--
--   This is the finite-order form of the induction proving Proposition 3.1 in $L^2$.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Flow.uniform_finite_varying_lowerCap_L2` in `lean/OAI/Geometry/IsometricImmersion/Caps/FiniteCapInduction.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Caps/FiniteCapInduction.lean; Section 3.3, proof of Proposition 3.1

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

theorem uniform_finite_varying_lowerCap_L2
    (G Z d c e0 kappa : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    {bStar : ℝ} (J : CapMetricJetBudget bStar) :
    ∀ k : ℕ, ∀ r : LowerCapRectangle bStar,
      (∀ b ∈ lowerCapMetricRequests k r, 0 ≤ J b.1 b.2) → ∃ H : ℝ≥0,
      ∀ (g : MetricField) (U : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
        (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
        CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
        FiniteCapMetricJets g Y J (lowerCapMetricRequests k r) → CoordinateL2Bound z (r.image Y) (k+8) H := by
  sorry

end SmoothLocal.Flow
end
end OAI
