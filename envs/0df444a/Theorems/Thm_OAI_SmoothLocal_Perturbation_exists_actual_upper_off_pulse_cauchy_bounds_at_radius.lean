-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_upper_off_pulse_cauchy_bounds_at_radius
-- name    : OAI.SmoothLocal.Perturbation.exists_actual_upper_off_pulse_cauchy_bounds_at_radius
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:38.142701+00:00
-- url     : https://prove2.me/theorems/635e05f6-470c-4f0c-b430-92439d1847cc
-- title:
--   All-order Cauchy data bounds at the upper pulse edge
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   With $g_*$, $G,d,\kappa,q_0,r,M$ as above and an order $K$, there is $B\ge0$ such that for all $N$ and $\delta>0$ and all sufficiently large $\tau$: for every patch perturbation $\eta$ and bounded admissible height $z$ of bound $M$ for $g=g_0+\eta$, where $g_0$ has the model curvature on an open $U\supseteq S$, $g$ has $C^8$ bound $G$, $|\det g|\ge d$, $|q(0)-q_0|\le1/(100L)$ and $g$ is within $\tau^{-\tau}$ in $C^\tau(S)$ of the test metric, one has for $|x|\le Lr/2$, $n\le K$,
--
--   $$\big\|D^n z_s(\cdot,\delta/\tau)(x)\big\|\le B,\qquad\big\|D^n\partial_\theta z_s(\cdot,\delta/\tau)(x)\big\|\le B.$$
--
--   This is the upper-edge assertion of Lemma 4.1, obtained from the upper cap.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Perturbation.exists_actual_upper_off_pulse_cauchy_bounds_at_radius` in `lean/OAI/Geometry/IsometricImmersion/Caps/ActualUpperOffPulseCauchy.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Caps/ActualUpperOffPulseCauchy.lean; Section 4.2, Lemma 4.1

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.Flow.Reflection SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Taylor
open SmoothLocal.Model

theorem exists_actual_upper_off_pulse_cauchy_bounds_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U : Set Coord) (z : Coord → ℝ),
          SmoothPositiveOn g0 U → SmoothPositiveOn (perturbedMetric g0 eta.val) U →
          IsOpen U → modelSquare ⊆ U →
          (∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 8 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
            ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
              (delta/(tau : ℝ))) x‖ ≤ B ∧
            ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
              (delta/(tau : ℝ))) x‖ ≤ B := by
  sorry

end SmoothLocal.Perturbation
end
end OAI
