-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_original_pulse_exclusion
-- name    : OAI.SmoothLocal.Perturbation.exists_original_pulse_exclusion
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:45.161907+00:00
-- url     : https://prove2.me/theorems/77ff8869-3870-4b18-a9a8-2eb3010e285d
-- title:
--   A thin pulse excludes bounded admissible heights near the test metric
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g_0,g_*$ be smooth and positive on an open $V\supseteq S$ with $g_0$ of model curvature, and fix $M>0$, $|q_0|\le1/20$. There is $r\in(0,1/2)$ with $Lr\le1/20$ such that for every $N>10$ there is $\delta\in(0,1/2]$ such that for all sufficiently large $\tau$: for every patch perturbation $\eta$ and every bounded admissible height $z$ with bound $M$ for $g=g_0+\eta$ satisfying $|q(0)-q_0|\le 1/(100L)$, it is not the case that
--
--   $$\|D^k(g_{ij}-(\tilde g_\tau)_{ij})\|_{\infty,S}\le\tau^{-\tau}\quad\text{for all }i,j\text{ and }k\le\tau.$$
--
--   Hence no metric in the class $\mathcal A_{M,q_0}$ lies this close to a test metric.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Perturbation.exists_original_pulse_exclusion` in `lean/OAI/Geometry/IsometricImmersion/Pulses/OriginalPulseExclusion.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Pulses/OriginalPulseExclusion.lean; Section 4.4, the contradiction of (4.20)-(4.21)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor SmoothLocal.Model

theorem exists_original_pulse_exclusion
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      ∀ N : ℕ, 10 < N → ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1/2 ∧
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            ¬ (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) := by
  sorry

end SmoothLocal.Perturbation
end
end OAI
