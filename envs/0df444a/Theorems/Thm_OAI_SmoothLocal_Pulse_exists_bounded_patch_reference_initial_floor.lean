-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Pulse_exists_bounded_patch_reference_initial_floor
-- name    : OAI.SmoothLocal.Pulse.exists_bounded_patch_reference_initial_floor
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:40.41584+00:00
-- url     : https://prove2.me/theorems/eb7673f9-0649-479d-b00f-91ed2d897676
-- title:
--   Lower bound for the sheared Hessian of the reference data at the lower pulse edge
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Fix $G\ge0$, $\kappa,d>0$, $M>0$, $|q_0|\le1/20$. There is $\tau_0\ge1$ such that for every $g_0,g_*$, every patch perturbation $\eta$, every bounded admissible height $z$ of bound $M$ for $g=g_0+\eta$, and every $r>0$, $N$, $\delta>0$, $\tau\ge\tau_0$ with $Lr\le1/20$, $r$ small, $\delta/\tau\le r$, $g$ of $C^4$ bound $G$ with $|\det g|\ge d$, and $|q(0)-q_0|\le 1/(100L)$: if $g$ is within $\tau^{-\tau}$ in $C^\tau(S)$ of the test metric $\tilde g_\tau$ built from $g_*$, then for $|x|<Lr$ the linear Cauchy polynomial $P$ of the sheared height at $\theta=-\delta/\tau$ satisfies
--
--   $$\frac{v_*^2}{4M}\le\big|H^{g_*}_{\xi\xi}[P]\big|\quad\text{at }(x,-\delta/\tau).$$
--
--   Thus the denominator of $Q_{g_*}$ stays away from zero at the data used to start the comparison.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Pulse.exists_bounded_patch_reference_initial_floor` in `lean/OAI/Geometry/IsometricImmersion/Pulses/ReferencePulseEdgeInitial.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Pulses/ReferencePulseEdgeInitial.lean; Section 4.3

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Perturbation
open SmoothLocal.Flow SmoothLocal.Taylor

theorem exists_bounded_patch_reference_initial_floor
    (G kappa d q0 : ℝ) (M : ℕ) (hG : 0 ≤ G)
    (hkappa : 0 < kappa) (hd : 0 < d) (hM : 0 < M) (hq0 : |q0| ≤ 1 / 20) :
    ∃ tau0 : ℕ, 1 ≤ tau0 ∧
      ∀ (g0 gStar : MetricField) (V : Set Coord) (eta : metricPatchSet g0 kappa)
        (z : Coord → ℝ) (r : ℝ) (N : ℕ) (delta : ℝ) (tau : ℕ),
      SmoothPositiveOn gStar V → IsOpen V → SmoothLocal.Flow.modelSquare ⊆ V →
      BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
      0 < r → boundedClassWidth kappa M * r ≤ 1 / 20 →
      heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
        (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤
          9 / (100 * boundedClassWidth kappa M) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ SmoothLocal.Flow.modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
      (∀ p ∈ SmoothLocal.Flow.modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
      |hessianQuotient (perturbedMetric g0 eta.val) z 0 - q0| ≤
        1 / (100 * boundedClassWidth kappa M) →
      0 < delta → tau0 ≤ tau → delta / (tau : ℝ) ≤ r →
      (∀ i j k, k ≤ tau → ∀ p ∈ SmoothLocal.Flow.modelSquare,
        ‖iteratedFDeriv ℝ k
          (fun a => perturbedMetric g0 eta.val a i j -
            testMetric gStar q0 (boundedClassWidth kappa M * r / 16) N delta (tau : ℝ) a i j) p‖ ≤
              metricApproximationAccuracy tau) →
      ∀ x ∈ Ioo (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r),
      (boundedClassSpeed kappa M)^2 / (4 * (M : ℝ)) ≤
        |covHessian (metricInShearCoordinates gStar q0)
          (linearCauchy (-delta / (tau : ℝ))
            (heightCauchyValue (heightInShearCoordinates z q0) (-delta / (tau : ℝ)))
            (heightCauchyVelocity (heightInShearCoordinates z q0) (-delta / (tau : ℝ))))
          ![x, -delta / (tau : ℝ)] 0 0| := by
  sorry

end SmoothLocal.Pulse
end
end OAI
