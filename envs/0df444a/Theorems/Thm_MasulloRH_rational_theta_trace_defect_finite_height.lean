-- Prove2me | Theorems.Thm_MasulloRH_rational_theta_trace_defect_finite_height
-- name    : MasulloRH.rational_theta_trace_defect_finite_height
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:19:11.533337+00:00
-- url     : https://prove2.me/theorems/23eaad84-c2ac-451a-926f-2f0fe9c13fc0
-- title:
--   A uniform finite-height error bound and off-line zero count from the actual theta trace defect
-- statement:
--   There is an absolute C>0 such that for every n and every actual regularized convolution on the polynomially weighted rational theta-annihilator for p=n+1, its geometric trace defect d_n is within C log(n+2)/(n+1) of the true off-critical-line resolvent mass D. For every height H≥0, the sum of multiplicities in any finite collection of off-line zeros up to H is at most 8(1+H²)(d_n+C log(n+2)/(n+1)). In particular an upper bound strictly below one excludes all such zeros. The common constant is existential; evaluation of a numerical threshold requires a bound for it.
-- source:
--   Quantitative refinement of the verified actual theta trace defect f6ad556e, using the unconditional full-strip explicit formula, the checked local Riemann–von Mangoldt zero count 2abaa392 and the real-lattice tail estimate 7bc6a754. The positive real resolvent kernel and qualitative detection were formalized in the Masullo RH mission. Masullo, The Music of the Primes, Chs. 10–12, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf.

import Definitions.Def_MasulloRH_RegularizedTrace
import Definitions.Def_MasulloRH_RationalThetaSpace
import Definitions.Def_MasulloGRH_HilbertNuclear
open MasulloRH MasulloGRH MeasureTheory Set Filter
open scoped Topology

theorem MasulloRH.rational_theta_trace_defect_finite_height :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∀ T : (rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1)),
      IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T →
      let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2}, (zeroResolventTerm (1/2) 3 z.val).re
      let d := (cutoffPolar n 3-(cutoffArch n 3+cutoffPrime n 3)).re-(operatorTrace T).re
      let err := C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1))
      |d-D| ≤ err ∧ ∀ H : ℝ, 0≤H →
        (∀ s : Finset {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
          (∀ z∈s, |z.val.val.im|≤H) →
          (∑ z ∈ s, (analyticOrderNatAt riemannZeta z.val.val:ℝ)) ≤ 8*(1+H^2)*(d+err)) ∧
        (8*(1+H^2)*(d+err)<1 → ∀ z : ℂ, riemannZeta z=0 → 0<z.re → z.re<1 →
          |z.im|≤H → z.re=1/2) := by sorry
