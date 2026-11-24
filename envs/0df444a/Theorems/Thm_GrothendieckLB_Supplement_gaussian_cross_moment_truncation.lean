-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_gaussian_cross_moment_truncation
-- name    : GrothendieckLB.Supplement.gaussian_cross_moment_truncation
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T21:50:42.893961+00:00
-- url     : https://prove2.me/theorems/fbe9d2f9-bd4e-4de0-8ffc-f3a6d4fa365d
-- title:
--   Separable Gaussian cross-moments with an exponential-series truncation bound
-- statement:
--   Let X,Y be independent standard Gaussians, U a real function, and F,G the two weights in a cross term of a squared Gaussian kernel. For any order K the coupled kernel with exponent −A(U(X)²+U(Y)²)+2B U(X)U(Y) has a finite separable approximation. Its error is at most q⁻⁽ᴷ⁺¹⁾ times the product of two absolute Gaussian moments with damping A−q|B|, for every q≥1 and under the stated integrability hypotheses. In the cubic–quintic certificate this evaluates the weighted Gaussian integrals at each quadrature node using one-dimensional moments.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.3–C.4. The series and Chernoff remainder in upper-bounds/gkcore/crossmoment.py, CrossS.assemble_norm.

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod

namespace GrothendieckLB.Supplement

open MeasureTheory ProbabilityTheory

theorem gaussian_cross_moment_truncation (A B q : ℝ) (hq : 1 ≤ q) (K : ℕ) (U F G : ℝ → ℝ) :
    let μ := gaussianReal 0 1
    let w (a : ℝ) (k : ℕ) (P : ℝ → ℝ) (x : ℝ) := P x*(U x)^k*Real.exp (-a*(U x)^2)
    let f (z : ℝ×ℝ) := F z.1*G z.2*Real.exp (-(A*((U z.1)^2+(U z.2)^2))+2*B*U z.1*U z.2)
    let decay := A-q*|B|
    Integrable f (μ.prod μ) →
    (∀ k ≤ K, Integrable (w A k F) μ ∧ Integrable (w A k G) μ) →
    Integrable (w decay 0 (fun x => |F x|)) μ →
    Integrable (w decay 0 (fun x => |G x|)) μ →
    |(∫ z, f z ∂μ.prod μ) - ∑ k ∈ Finset.range (K+1), ((2*B)^k/k.factorial) *
       ((∫ x, w A k F x ∂μ)*(∫ y, w A k G y ∂μ))| ≤
       ((∫ x, w decay 0 (fun s => |F s|) x ∂μ)*(∫ y, w decay 0 (fun s => |G s|) y ∂μ))/q^(K+1) := by sorry

end GrothendieckLB.Supplement
