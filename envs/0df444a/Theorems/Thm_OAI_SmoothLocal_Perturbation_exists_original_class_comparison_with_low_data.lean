-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_original_class_comparison_with_low_data
-- name    : OAI.SmoothLocal.Perturbation.exists_original_class_comparison_with_low_data
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:28:18.805612+00:00
-- url     : https://prove2.me/theorems/bc6d0d45-e9a8-4cb8-adc6-e62ba3c6e41c
-- title:
--   Consolidated pulse estimates for the original metric class
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $g_0,g_*$ be smooth and positive on an open $V\supseteq S$, with $g_0$ of model curvature with parameter $\kappa$, and fix $M>0$, $|q_0|\le1/20$. There are $G,d,r$ with $0<r<1/2$ and $Lr\le 1/20$, $r$ small, such that $g_*$ has $C^8$ bound $G$ and $\det g_*\ge d$ on $S$, all metrics close to a test metric inherit these bounds, and for all orders $K$ uniform bounds $B$ hold for Cauchy data at both pulse edges, for every patch perturbation and bounded admissible height of bound $M$ whose metric is within $\tau^{-\tau}$ of the test metric, $N>10$, $\delta>0$ and large $\tau$. Moreover for each $N>10$ there are constants such that for the Taylor comparison $P$, the residual, source and gradient bounds of the preceding results hold, the source is continuous on the strip of half-width $Lr/16$, and there is $c_3>0$, independent of small $\delta$, with
--
--   $$c_3\,\delta\,\tau^{1-N}\le\big|\mathrm{moment}_{\delta,\tau}(F)\big|,$$
--
--   where the moment is the integral of the source against $\chi_0(\xi)\cos(\tau\xi)$ over the strip.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Perturbation.exists_original_class_comparison_with_low_data` in `lean/OAI/Geometry/IsometricImmersion/Comparison/OriginalClassComparisonWithLow.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Comparison/OriginalClassComparisonWithLow.lean; Section 4, assembling (4.18)-(4.21)

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

theorem exists_original_class_comparison_with_low_data
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ G d r : ℝ, 0 < G ∧ 0 < d ∧ 0 < r ∧ r < 1/2 ∧
      (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      (∀ a : ℝ, 0 < a → ∀ N : ℕ, 10 < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop,
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) ∧
            (∀ p ∈ modelSquare, d ≤ |(gTau p).det|)) ∧
      boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      (∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 10 < N → ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B) ∧
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B)) ∧
      ∀ N : ℕ, 10 < N → ∃ C Csource Cgradient c3 : ℝ,
        0 ≤ C ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧ 0 < c3 ∧
        (∀ K : ℕ, ∃ CP : ℝ, 0 ≤ CP ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
            ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
              BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
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
              (∀ j ≤ K, ∀ p : Coord, |p 0| ≤ boundedClassWidth kappa M*r/2 →
                |p 1| ≤ delta/(tau : ℝ) → ‖iteratedFDeriv ℝ j P p‖ ≤ CP) ∧
              CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) K CP) ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
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
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              P ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 P ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ poly : Polynomial ℝ, poly.natDegree ≤ N+1 ∧ ∀ t, poly.eval t = P ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P ![x,t] 0 0| ∧
                |qResidual gs P ![x,t]| ≤ C/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs P) (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs P)| ≤
              (2*C*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) ∧
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N) ∧
            (∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*delta*(tau : ℝ)/(tau : ℝ)^N) ∧
            ContinuousOn (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            c3*delta*(tau : ℝ)/(tau : ℝ)^N ≤
              |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ)
                (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)| := by
  sorry

end SmoothLocal.Perturbation
end
end OAI
