-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_no_small_coarse_energy
-- name    : OAI.TwoPointCorrelations.mrt_no_small_coarse_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:27.201395+00:00
-- url     : https://prove2.me/theorems/8c9f19e1-7177-4ed3-a7af-3496aa45164f
-- title:
--   Under the sparse prime input, the coarse extra-prime polynomial has small mean square off the small bands
-- statement:
--   Assume `HalaszPrimeSparseInput`. Then there is $C>0$ such that for all sufficiently large $L$: for all sets $V_i$, every $F$ bounded by $1$ on positive integers, naturals $j<J$, reals $1\le P\le Q$ with $\log Q\ge1$ and `mrtBaseResolution P Q (1/100)` $\ge2$, with $V_{j+1}$ a set of primes in $[\mathrm{lo}_{j+1},\mathrm{up}_{j+1}]$, $200\log L+1\le\log\mathrm{lo}_{j+1}$ and $\log\mathrm{up}_{j+1}\le\sqrt L$; every $N\ge e^L$; and every measurable $E\subseteq(-e^L,e^L]$ contained in the no-small-band set `mrtNoSmallBand (mrtLogFamilyBins P Q (1/100)) (mrtLogFamilyPolynomial V F P Q (1/100)) (mrtLogFamilyThreshold P Q (1/100)) J`, such that for every extra-prime log bin $k$ and $t\in E$ with $|\mathcal P_k(t)|\ge L^{-100}$ the cofactor polynomial `mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J) V F) N (e^{k/L^{1/80}}) t` has modulus at most $2L^{-1/40}$ (here $A$ is the extra prime band $(e^{2L^{79/80}},e^{L/\log L}]$ and $\mathcal P_k$ = `mrtLogPrimePolynomial A F L^{1/80} k`):
--
--   $$\int_E\big|\texttt{mrtExtraCoarsePolynomial}\ L\ (Icc\ 1\ J)\ V\ F\ N\ t\big|^2dt\le C\,L^{-1/80}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_no_small_coarse_energy`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory
open scoped Classical

theorem mrt_no_small_coarse_energy (hprime : HalaszPrimeSparseInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
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
    (∫ t in E, ‖mrtExtraCoarsePolynomial L (Icc 1 J) V F N t‖^2) ≤ C*L^(-1/80:ℝ) := by
  sorry

end OAI.TwoPointCorrelations
