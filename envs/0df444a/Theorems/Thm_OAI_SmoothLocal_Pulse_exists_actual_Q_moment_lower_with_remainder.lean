-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Pulse_exists_actual_Q_moment_lower_with_remainder
-- name    : OAI.SmoothLocal.Pulse.exists_actual_Q_moment_lower_with_remainder
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:56.339995+00:00
-- url     : https://prove2.me/theorems/612a269e-659d-4f88-918c-305471d7f6f3
-- title:
--   Lower bound for the oscillatory moment of the $Q$-forcing
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Fix bounds $B,B_{\mathrm{compare}},B_Q,D,A,D_{\mathrm{ref}},C_{\mathrm{ref}}$, $d,d_{\mathrm{compare}},c,e$, $a>0$ and $N>1$. There are $c_3>0$ and $H,C_{\mathrm{first}},C_{\mathrm{test}},C_{\mathrm{compare}}\ge0$ such that for each $\delta>0$ there is $T\ge1$ such that for $\tau\ge T$, all metrics $g_*,g_\tau$ smooth and positive on an open $U$ (the test metric also), $q_0$ real, $z$ smooth on $U$, and small $\epsilon,\epsilon_Q$: if the pointwise $Q$-pulse bounds hold on the strip, $H_{\xi\xi}\ne0$ on the strip, and $E\ge e$, $\det g\le D_{\mathrm{ref}}$, $|H_{\xi\xi}|\le C_{\mathrm{ref}}$ there for $g_*$, then
--
--   $$c_3\frac{\delta\tau}{\tau^N}-\mathrm{rem}(\epsilon,\epsilon_Q)\frac{2\delta}\tau\int\chi\le\big|\mathrm{moment}_{\delta,\tau}(F_{g_\tau,g_*,z})\big|,$$
--
--   where $F_{g_\tau,g_*,z}$ is the sheared $Q$-forcing, and $\mathrm{rem}$ is an explicit budget linear in the small parameters.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Pulse.exists_actual_Q_moment_lower_with_remainder` in `lean/OAI/Geometry/IsometricImmersion/Estimates/ActualQMomentLower.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Estimates/ActualQMomentLower.lean; Section 4.4, (4.18) and (4.21)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_Q_moment_lower_with_remainder
    (B Bcompare BQ D A Dref Cref : ℝ) {d dcompare c e : ℝ}
    (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c) (he : 0 < e)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ c3 H Cfirst Ctest Ccompare : ℝ,
      0 < c3 ∧ 0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          ∀ epsilon epsilonQ : ℝ, 0 ≤ epsilon → 0 ≤ epsilonQ →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            (∀ p ∈ pulseStrip a delta tau,
              QPulsePointBounds gStar gTau z U q0 a delta tau N
                B Bcompare BQ D A d dcompare c epsilon epsilonQ p) →
            (∀ p ∈ pulseStrip a delta tau,
              covHessian (metricInShearCoordinates gTau q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0) →
            (∀ p ∈ pulseStrip a delta tau,
              e ≤ heightEnergy (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p) →
            (∀ p ∈ pulseStrip a delta tau, (metricInShearCoordinates gStar q0 p).det ≤ Dref) →
            (∀ p ∈ pulseStrip a delta tau,
              |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0| ≤ Cref) →
            c3*delta*tau/tau^N-
                qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
                  (2*delta/tau)*(∫ x : ℝ, axisBump a x) ≤
              |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| := by
  sorry

end SmoothLocal.Pulse
end
end OAI
