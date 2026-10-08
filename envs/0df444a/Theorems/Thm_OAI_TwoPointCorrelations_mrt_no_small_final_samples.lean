-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_no_small_final_samples
-- name    : OAI.TwoPointCorrelations.mrt_no_small_final_samples
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:40.72335+00:00
-- url     : https://prove2.me/theorems/15ad5614-1931-40d1-a2ba-862c0a9fcac6
-- title:
--   Well-spaced points avoiding the small bands are at most #bins · e^{99L/200} in number
-- statement:
--   For all sufficiently large $L$: for all sets $V_i$, every $F$ bounded by $1$ on positive integers, naturals $j<J$, reals $P,Q$ with $\log Q\ge1$, `mrtBaseResolution P Q (1/100)` $\ge2$, $V_{j+1}$ a set of primes in $[\mathrm{lo}_{j+1},\mathrm{up}_{j+1}]$ with $200\log L+1\le\log\mathrm{lo}_{j+1}$ and $\log\mathrm{up}_{j+1}\le\sqrt L$; every $T\in(1,e^L]$; and every finite set $S$ of reals with $|t|\le T$, pairwise distances at least $1$, and $S$ inside the no-small-band set `mrtNoSmallBand (mrtLogFamilyBins P Q (1/100)) (mrtLogFamilyPolynomial V F P Q (1/100)) (mrtLogFamilyThreshold P Q (1/100)) J`:
--
--   $$\#S\le\#\texttt{mrtLogFamilyBins}(P,Q,\tfrac1{100},j)\cdot e^{99L/200}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_no_small_final_samples`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical

theorem mrt_no_small_final_samples :
    ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ T : ℝ, 1 < T → T ≤ Real.exp L → ∀ S : Finset ℝ,
    (∀ t ∈ S, |t| ≤ T) →
    (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
    (∀ t ∈ S, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (S.card:ℝ) ≤ (mrtLogFamilyBins P Q (1/100) j).card *
      Real.exp ((99/200:ℝ)*L) := by
  sorry

end OAI.TwoPointCorrelations
