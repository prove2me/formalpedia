-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_bounded_patch_cauchy_bound
-- name    : OAI.SmoothLocal.Perturbation.exists_bounded_patch_cauchy_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:22.180893+00:00
-- url     : https://prove2.me/theorems/d42eb554-82bd-4cd7-8201-e5182278e187
-- title:
--   All-order Cauchy data bound on a cut, from all-order bounds on the lower cut
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Fix $G,d,\kappa,q_0,r,C\ge0$ as above, with $M>0$, $r<1/2$, $|q_0|\le1/20$, $Lr\le1/20$ and $r$ small, and an order $K$. There is $B\ge0$ such that for every patch perturbation $\eta$, every bounded admissible height $z$ with bound $M$, and every $b\in[-r,0]$: if $g=g_0+\eta$ has $C^4$ bound $G$ and $|\det g|\ge d$ on $S$, $|q(0)-q_0|\le1/(100L)$, the sheared metric has derivatives bounded by $C$ through order $\max(9,K+3)$ on the slab between $\theta=-r$ and $\theta=b$, and the sheared height has derivatives bounded by $A$ through order $\max(8,K+2)$ on the cut $\theta=-r$, then for $|x|\le Lr/2$ and $n\le K$,
--
--   $$\big\|D^n\big[z_s(\cdot,b)\big](x)\big\|\le B,\qquad\big\|D^n\big[\partial_\theta z_s(\cdot,b)\big](x)\big\|\le B,$$
--
--   where $z_s$ is the sheared height. It is the step from the cut $\theta=-r$ to any later cut below the pulse.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Perturbation.exists_bounded_patch_cauchy_bound` in `lean/OAI/Geometry/IsometricImmersion/Caps/BoundedPatchCauchy.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Caps/BoundedPatchCauchy.lean; Section 4.2, proof of Lemma 4.1

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix NNReal

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_bounded_patch_cauchy_bound
    (G d kappa q0 r C : ℝ) (M : ℕ) (A : ℝ≥0) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hr : 0 < r) (hrhalf : r < 1/2)
    (hC : 0 ≤ C) (hq0 : |q0| ≤ 1/20)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M)) (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa)
      (z : Coord → ℝ) (b : ℝ),
      BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z → -r ≤ b → b ≤ 0 →
      (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
      |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
      (∀ i j, CoordinateBound (fun p => metricInShearCoordinates (perturbedMetric g0 eta.val) q0 p i j)
        (shrinkingSlab (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r)
          (-r) b (boundedClassWidth kappa M/4)) (max 9 (K+3)) C) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (K+2) → ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r →
        |iteratedCoordPartial ds (heightInShearCoordinates z q0) (coordinatePoint x (-r))| ≤ (A : ℝ)) →
      ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
        ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0) b) x‖ ≤ B ∧
        ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0) b) x‖ ≤ B := by
  sorry

end SmoothLocal.Perturbation
end
end OAI
