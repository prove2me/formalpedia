-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_reference_segment_at_radius
-- name    : OAI.SmoothLocal.Perturbation.exists_actual_reference_segment_at_radius
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:47.108877+00:00
-- url     : https://prove2.me/theorems/7223f032-93b4-404e-8ef2-3b532f2a1867
-- title:
--   Ellipticity margins along the segment joining the comparison and height jets
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   With $g_*$, $G,d,\kappa,q_0,r,M$ as above, where $g_*$ also has $C^2$ bound $G$ and $\det g_*\ge d$ on $S$, and $N>2$, there are $C\ge0$ and $A\ge1$ such that for $0<\delta\le1/2$ and all sufficiently large $\tau$: for every patch perturbation $\eta$, flow data and bounded admissible height $z$ of bound $M$ with the usual bounds and $g$ within $\tau^{-\tau}$ of the test metric, for $P$ the Taylor approximation of the sheared height for $g_*$, at every $p$ in the strip of half-width $Lr/2$ and every $\sigma\in[0,1]$, the jet $J_\sigma$ on the segment between $P$ and $z_s$ satisfies
--
--   $$\frac{v_*^2}{4M}\le|\mathrm{den}_{g_*}(J_\sigma)|\le A,\quad\frac1{2M}\le E_{g_*}(J_\sigma),\quad\frac{v_*^2}{4M^2A^2}\le S_1(J_\sigma),\quad\frac{\kappa}{8MA^2}\le\frac{P_1^2}{4}+S_1,$$
--
--   where $v_*$ and $L$ are the class speed and width. It justifies the mean-value linearization in (4.16).
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Perturbation.exists_actual_reference_segment_at_radius` in `lean/OAI/Geometry/IsometricImmersion/Coordinates/ActualReferenceSegment.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Coordinates/ActualReferenceSegment.lean; Section 4.3, discussion of (4.16)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_reference_segment_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N : ℕ) (hN : 2 < N) :
    ∃ C A : ℝ, 0 ≤ C ∧ 1 ≤ A ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
          (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          let zs := heightInShearCoordinates z q0
          let gs := metricInShearCoordinates gStar q0
          let P := taylorApproximation gs (-delta/(tau : ℝ))
            (heightCauchyValue zs (-delta/(tau : ℝ)))
            (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
          ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
          CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) 3 C ∧
          (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            ∀ sigma ∈ Icc (0 : ℝ) 1,
              (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) ≤
                |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ∧
              |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ≤ A ∧
              (1/(M : ℝ))/2 ≤ stateEnergy gs (qHeightJetSegment P zs sigma p) ∧
              ((((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))*(1/(M : ℝ)))/2)/A^2 ≤
                qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p) ∧
              (((kappa/2)/2)*((1/(M : ℝ))/2))/A^2 ≤
                (qFirstCoefficient gs 4 (qHeightJetSegment P zs sigma p)/2)^2+
                  qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p)) := by
  sorry

end SmoothLocal.Perturbation
end
end OAI
