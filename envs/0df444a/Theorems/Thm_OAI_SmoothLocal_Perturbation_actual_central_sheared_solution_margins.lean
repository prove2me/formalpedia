-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Perturbation_actual_central_sheared_solution_margins
-- name    : OAI.SmoothLocal.Perturbation.actual_central_sheared_solution_margins
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:27:33.531418+00:00
-- url     : https://prove2.me/theorems/817c38dd-a4f0-4f15-a258-91923d86d552
-- title:
--   Margins of a bounded admissible height in sheared coordinates near the centre
-- statement:
--   Notation. $S=[-3,3]^2$ is the model square; a metric is a smooth positive matrix field $g$; $z$ is a scalar height; $H=\nabla_g^2z$ is its covariant Hessian; $K_g$ is the Gaussian curvature; $E=\det g\,(1-|dz|_g^2)$; $q=H_{xy}/H_{yy}$ is the Hessian quotient; $\kappa(x^2-h(y))$ is the model curvature; the patch box and the central box are the squares $[-1/10,1/10]^2$ and $[-1/5,1/5]^2$; the sheared coordinates are $\xi=x,\ \theta=y+q_0x$, with sheared height $z_s$; $L$ and $v_*$ are the class width and speed of (4.2); $\tilde g_\tau$ is the test metric (4.12) built from $g_*$; a bounded admissible height of bound $M$ is an admissible height with (4.1).
--
--   Let $\eta$ lie in the patch perturbation set for $g_0,\kappa$, and let $z$ be a bounded admissible height with bound $M$ for $g=g_0+\eta$. Let $L$ and $v_*$ be the width and speed attached to $(\kappa,M)$ by (4.2). Assume $Lr\le1/20$, $|q_0|\le1/20$, that $r$ is small with respect to the $C^1$ bound of $q$, that $g$ has $C^4$ bound $G$ and $|\det g|\ge d$ on $S$, and that $|q(0)-q_0|\le 1/(100L)$. Then for every $p$ with $|p_0|\le Lr$, $|p_1|\le r$, in the sheared coordinates $\xi=x$, $\theta=y+q_0x$, the point lies in $S$ and
--
--   $$\frac{v_*^2}{2M}\le|H_{\xi\xi}|,\quad \frac1M\le|H_{\theta\theta}|,\quad \frac1M\le E,\quad K\le-\frac\kappa2,\quad \det H=KE,\quad q^2+KG<0.$$
--
--   These are the uniform margins that make the Darboux equation hyperbolic in the thin slab.
--
--   **Formalization Note.** This is the upstream Lean declaration `OAI.SmoothLocal.Perturbation.actual_central_sheared_solution_margins` in `lean/OAI/Geometry/IsometricImmersion/Coordinates/ActualCentralShearMargins.lean`, stated verbatim; the Lean statement is authoritative for the precise hypotheses. It is an intermediate result of OpenAI's formalization.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Lean: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Geometry/IsometricImmersion/ (Apache License 2.0), file lean/OAI/Geometry/IsometricImmersion/Coordinates/ActualCentralShearMargins.lean; Section 4.1, (4.4)-(4.6)

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem actual_central_sheared_solution_margins
    {g0 : MetricField} {kappa q0 r G d : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z)
    (hG : 0 ≤ G) (hd : 0 < d) (hkappa : 0 < kappa) (hr : 0 ≤ r)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hcenter : |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
      1/(100*boundedClassWidth kappa M))
    {p : Coord} (hx : |p 0| ≤ boundedClassWidth kappa M*r) (ht : |p 1| ≤ r) :
    let g := metricInShearCoordinates (perturbedMetric g0 eta.val) q0
    let zs := heightInShearCoordinates z q0
    inverseShearCoordinates q0 p ∈ modelSquare ∧
      (boundedClassSpeed kappa M)^2/(2*(M : ℝ)) ≤ |covHessian g zs p 0 0| ∧
      1/(M : ℝ) ≤ |covHessian g zs p 1 1| ∧
      1/(M : ℝ) ≤ heightEnergy g zs p ∧
      gaussianCurvature g p ≤ -(kappa/2) ∧
      (covHessian g zs p).det = gaussianCurvature g p*heightEnergy g zs p ∧
      (hessianQuotient g zs p)^2+gaussianCurvature g p*darbouxG g zs p < 0 := by
  sorry

end SmoothLocal.Perturbation
end
end OAI
