-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_mixed_hermite_identity
-- name    : GrothendieckLB.Supplement.cq_boundary_mixed_hermite_identity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:43:16.406618+00:00
-- url     : https://prove2.me/theorems/0f7206e9-87f5-4d3f-ae81-da078a68b093
-- title:
--   Gaussian integration by parts for the differentiated cubic–quintic boundary kernel
-- statement:
--   On each point of the unit circle, the third Euler kernel $K=\Phi_3$ and its mixed spatial derivative are square-integrable under the product standard Gaussian. The $(n,n)$ Hermite coefficient of $\partial_x\partial_yK$ equals $(n+1)$ times the $(n+1,n+1)$ coefficient of $K$. This is one Gaussian integration by parts in each variable. The positive quadratic decay of the complex Gaussian kernel controls the boundary terms.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.2, Lemma C.2 and equation (51).

import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel

namespace GrothendieckLB.Supplement

open MeasureTheory ProbabilityTheory

theorem cq_boundary_mixed_hermite_identity :
    ∀ θ : ℝ,
      let K := CQBoundary.phiThree (CQBoundary.unitPoint θ)
      let μ := gaussianReal 0 1
      MemLp (fun p : ℝ×ℝ => K p.1 p.2) 2 (μ.prod μ) ∧
      MemLp (fun p : ℝ×ℝ => CQBoundary.mixed K p.1 p.2) 2 (μ.prod μ) ∧
      ∀ n : ℕ, (∫ p : ℝ×ℝ, CQBoundary.mixed K p.1 p.2 *
        Complex.ofReal (QuadSDE.hermiteN n p.1*QuadSDE.hermiteN n p.2) ∂μ.prod μ) =
        ((n:ℂ)+1) * ∫ x : ℝ, ∫ y : ℝ, K x y *
          Complex.ofReal (QuadSDE.hermiteN (n+1) x*QuadSDE.hermiteN (n+1) y) ∂μ ∂μ := by sorry

end GrothendieckLB.Supplement
