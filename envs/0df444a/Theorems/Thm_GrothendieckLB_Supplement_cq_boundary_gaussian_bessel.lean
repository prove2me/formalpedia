-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_gaussian_bessel
-- name    : GrothendieckLB.Supplement.cq_boundary_gaussian_bessel
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:25:21.806851+00:00
-- url     : https://prove2.me/theorems/3f026499-a82b-4500-b4fc-e9d7aaa4376b
-- title:
--   Gaussian Bessel bounds for the differentiated cubic–quintic kernel
-- statement:
--   For $K=\Phi_3(e^{i\theta})$, the zeroth diagonal Hermite coefficient has squared norm at most $\|K\|_2^2$. Every finite sum of $n^2|\widehat K_{nn}|^2$ over positive modes is bounded by $\|\partial_x\partial_y K\|_2^2$. Gaussian integration by parts identifies the positive modes with the shifted Hermite coefficients of the mixed derivative, to which Bessel's inequality applies. The combined energy is the stated sum of the two squared norms.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix C.2–C.4, equations (51)–(53).

import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel

namespace GrothendieckLB.Supplement

open MeasureTheory ProbabilityTheory

theorem cq_boundary_gaussian_bessel :
    ∀ θ : ℝ,
      let K := CQBoundary.phiThree (CQBoundary.unitPoint θ)
      let μ := gaussianReal 0 1
      let d := fun n : ℕ => ∫ x : ℝ, ∫ y : ℝ, K x y * ↑(QuadSDE.hermiteN n x * QuadSDE.hermiteN n y) ∂μ ∂μ
      let u := ∫ x : ℝ, ∫ y : ℝ, ‖K x y‖^2 ∂μ ∂μ
      let v := ∫ x : ℝ, ∫ y : ℝ, ‖CQBoundary.mixed K x y‖^2 ∂μ ∂μ
      u+4*v=CQBoundary.energy θ ∧ ‖d 0‖^2≤u ∧
        ∀ N : ℕ, (∑ k ∈ Finset.range N, ((k:ℝ)+1)^2*‖d (k+1)‖^2)≤v := by sorry

end GrothendieckLB.Supplement
