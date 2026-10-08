-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_actual_bin_moment_sum
-- name    : OAI.TwoPointCorrelations.mrt_actual_bin_moment_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:16.313283+00:00
-- url     : https://prove2.me/theorems/81f7f455-7f40-4359-86f7-991ed88ed450
-- title:
--   The total mixed bin cost of two consecutive Matomäki–Radziwiłł bands
-- statement:
--   Let $\eta\in(0,1/6]$, $j\in\mathbb N$, and reals $P,Q,\tau,H_0,H_1$ with $\log P\ge2$, $\log Q\ge1$, $8192(\log\log Q+1)\le\eta\log P$, $H_0,H_1\ge2$, $\tau\ge0$. Write $\mathrm{lo}_i,\mathrm{up}_i$ for the band endpoints (`mrtBandLower P Q i`, `mrtBandUpper Q i`), $\mathcal B_i(H)=\{\lfloor H\log\mathrm{lo}_i\rfloor,\dots,\lfloor H\log\mathrm{up}_i\rfloor\}$ (`mrtLogBins`) and $\ell_H(k)=e^{k/H}$ (`mrtPrimeLogLower`). Then, with $\theta=\eta/(2(j+2)^2)$,
--
--   $$2\sum_{b\in\mathcal B_{j+1}(H_0)}\#\mathcal B_{j+2}(H_1)\sum_{k\in\mathcal B_{j+2}(H_1)}c_{\eta,j}\big(\tau,\ell_{H_0}(b),\ell_{H_1}(k)\big)\le64e^{11}(\tau+1)(H_0\log\mathrm{up}_{j+1}+1)(H_1\log\mathrm{up}_{j+2}+1)\frac{H_1}{\theta}\,\mathrm{lo}_{j+2}^{-\theta},$$
--
--   where $c_{\eta,j}$ = `mrtMixedBinCost η j` is the explicit bin cost of the bundle (built from `mrtFrequencyExponent` and `mrtAmplificationOrder`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_actual_bin_moment_sum`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical

theorem mrt_actual_bin_moment_sum {η P Q τ H₀ H₁ : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH₀ : 2 ≤ H₀) (hH₁ : 2 ≤ H₁) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ mrtLogBins H₀ (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1)),
      ((mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))).card : ℝ) *
        ∑ k ∈ mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2)),
          mrtMixedBinCost η j τ (mrtPrimeLogLower H₀ b) (mrtPrimeLogLower H₁ k) ≤
      64 * Real.exp 11 * (τ + 1) *
        (H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1) *
        (H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1) *
        (H₁ / (η / (2 * ((j : ℝ) + 2) ^ 2))) *
        (mrtBandLower P Q (j + 2)) ^ (-(η / (2 * ((j : ℝ) + 2) ^ 2))) := by
  sorry

end OAI.TwoPointCorrelations
