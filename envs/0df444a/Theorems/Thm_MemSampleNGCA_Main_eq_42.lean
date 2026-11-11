-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_eq_42
-- name    : MemSampleNGCA.Main.eq_42
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:42:31.554194+00:00
-- url     : https://prove2.me/theorems/46751960-a168-4f83-84d5-f19a33ed484e
-- title:
--   §C.1.2, Eq. (42) — T_KL(2h) ≤ log T_2(2h) ≤ 2C^m(128h/d)^m + 4Me^{−6h} for 1 ≤ h ≤ d/256
-- statement:
--   Let $A$ satisfy Assumptions (A1)–(A2) with parameters $M$, $C>0$ and $m$, and let $T_{KL}$ and $T_2$ be the functionals (17a)–(17b) of the NGCA family ($\Theta=S^{d-1}$ with the uniform $\pi$, $P_0=N(0,I_d)$, $P_\theta=P_{A,\theta}$). For every $1\le h\le d/256$,
--   $$T_{KL}(2h)\le\log T_2(2h)\le2C^m\Big(\frac{128h}{d}\Big)^m+4Me^{-6h}.$$
--
--   The display bounds the diffuse-information term of Theorem B.1 for NGCA. It combines $\mathrm{KL}\le\log(1+\chi^2)$ with Proposition C.3 at $q=2$, $\delta=128h/d$.
--
--   Differences from the source:
--   - encoding: T_KL(2h), T_2(2h) for the NGCA instance → TKL / Tq (sphereUnif d) (gammaD d) (ngcaDensity d A); reason: as in Proposition C.3
--   - encoding: the chain T_KL ≤ log T_2 ≤ bound of reals → a conjunction of two inequalities in EReal, with T_KL coerced from ℝ≥0∞ and log as ENNReal.log; reason: equal values for finite positive T_2; no junk value at 0 or ∞
--   - encoding: Assumptions (A1)–(A2) of Assumption C.1 → AssumptionA1, AssumptionA2; M ≥ 1 not stated separately; reason: as in Proposition C.3
--   - generalization: m ∈ ℕ → every m : ℕ, including m = 0; reason: as in Proposition C.3
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 28 (PDF 30), §C.1.2, Eq. (42)

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming
import Definitions.Def_MemSampleNGCA_Main_NGCA
import Definitions.Def_MemSampleNGCA_Main_Framework

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- §C.1.2, Eq. (42) (p. 28, PDF 30): if `A` satisfies Assumptions (A1)–(A2), then for every
`1 ≤ h ≤ d/256`, the NGCA functionals (17a)–(17b) satisfy
`T_KL(2h) ≤ log T_2(2h) ≤ 2 C^m (128h/d)^m + 4M e^{−6h}`. -/
theorem eq_42 (d m : ℕ) (C M : ℝ) (A : Measure ℝ) [IsProbabilityMeasure A]
    (hA1 : AssumptionA1 M A) (hA2 : AssumptionA2 C m A)
    (h : ℝ) (hh₁ : 1 ≤ h) (hh₂ : h ≤ (d : ℝ) / 256) :
    ((TKL (sphereUnif d) (gammaD d) (ngcaDensity d A) (2 * h) : ℝ≥0∞) : EReal) ≤
        ENNReal.log (Tq (sphereUnif d) (gammaD d) (ngcaDensity d A) 2 (2 * h)) ∧
      ENNReal.log (Tq (sphereUnif d) (gammaD d) (ngcaDensity d A) 2 (2 * h)) ≤
        ((2 * C ^ m * (128 * h / d) ^ m + 4 * M * Real.exp (-6 * h) : ℝ) : EReal) := by sorry

end MemSampleNGCA.Main
