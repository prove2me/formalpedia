-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_no_small_energy_sharp
-- name    : OAI.TwoPointCorrelations.mrt_no_small_energy_sharp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:38.219514+00:00
-- url     : https://prove2.me/theorems/f99c5332-1e58-4697-91b7-eb75c31c0d84
-- title:
--   Under the sparse prime input, the typical dyadic polynomial has mean square ≪ log L / L^{1/80} off the small bands
-- statement:
--   Assume `HalaszPrimeSparseInput`. Then there is $C>0$ such that for all sufficiently large $L$: for all sets $V_i$ with $V_i$ ($1\le i\le J$) consisting of primes at most $e^{\sqrt L}$, every multiplicative $F$ bounded by $1$ on positive integers, naturals $j<J$, reals $1\le P\le Q$ with $\log Q\ge1$, `mrtBaseResolution P Q (1/100)` $\ge2$, $V_{j+1}$ inside $[\mathrm{lo}_{j+1},\mathrm{up}_{j+1}]$, $200\log L+1\le\log\mathrm{lo}_{j+1}$ and $\log\mathrm{up}_{j+1}\le\sqrt L$; every $N\ge e^L$; and every measurable $E\subseteq(-e^L,e^L]$ inside the no-small-band set and satisfying the same cofactor condition at the extra prime log bins as in `mrt_no_small_coarse_energy`:
--
--   $$\int_E|D_N(t)|^2dt\le C\,\frac{\log L}{L^{1/80}},$$
--
--   where $D_N$ is the dyadic polynomial $\sum_{N<n\le2N}\frac{G(n)}nn^{-it}$ of $G$ = `mrtTypicalCoefficient (Icc 1 J) V F`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_no_small_energy_sharp`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open scoped Classical

theorem mrt_no_small_energy_sharp (hprime : HalaszPrimeSparseInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), Multiplicative F → OneBounded F →
    ∀ J j : ℕ, j < J →
    (∀ i ∈ Icc 1 J, ∀ p ∈ V i, p.Prime) →
    (∀ i ∈ Icc 1 J, ∀ p ∈ V i, (p:ℝ) ≤ Real.exp (Real.sqrt L)) →
    ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ N : ℕ, Real.exp L ≤ N → ∀ E : Set ℝ,
    MeasurableSet E → E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) →
    (∀ t ∈ E, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
        (mrtExtraPrimeUpper L), ∀ t ∈ E,
      L^(-100:ℝ) ≤ ‖mrtLogPrimePolynomial
        (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
          (mrtExtraPrimeResolution L) k t‖ →
      ‖mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
        (mrtTypicalCoefficient (Icc 1 J) V F) N
        (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖ ≤ 2*L^(-1/40:ℝ)) →
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2) ≤
      C*Real.log L/L^(1/80:ℝ) := by
  sorry

end OAI.TwoPointCorrelations
