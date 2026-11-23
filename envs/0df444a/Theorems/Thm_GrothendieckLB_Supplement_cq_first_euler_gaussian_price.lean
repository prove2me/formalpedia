-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_cq_first_euler_gaussian_price
-- name    : GrothendieckLB.Supplement.cq_first_euler_gaussian_price
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T20:22:55.83982+00:00
-- url     : https://prove2.me/theorems/d1ac2fdb-ea77-459b-b7a0-e890bcac23b4
-- title:
--   First Euler derivative of the cubic–quintic correlation by Gaussian differentiation
-- statement:
--   On a real neighborhood of zero, the first Euler derivative of the cubic–quintic sign correlation equals the diagonal Hermite trace of its explicitly differentiated Gaussian threshold kernel. Differentiating in the primary correlation gives the bivariate Gaussian density at the thresholds, and differentiating the secondary correlation gives the mixed threshold derivative.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.2, Lemmas C.1–C.2 and equations (47)–(50).

import Definitions.Def_GrothendieckLB_Supplement_cqBoundaryEulerKernel
import Definitions.Def_GrothendieckLB_Supplement_cqCorr

namespace GrothendieckLB.Supplement

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem cq_first_euler_gaussian_price :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (fun t : ℝ => ∑' n : ℕ, (-(t:ℂ))^n * (∫ x : ℝ, ∫ y : ℝ,
      CQBoundary.phiOne (t:ℂ) x y * Complex.ofReal (QuadSDE.hermiteN n x * QuadSDE.hermiteN n y)
      ∂gaussianReal 0 1 ∂gaussianReal 0 1)) =ᶠ[𝓝 0] fun t : ℝ => Complex.ofReal (t*deriv H t) := by sorry

end GrothendieckLB.Supplement
