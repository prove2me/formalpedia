-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_mixed_real_bin_separation
-- name    : OAI.TwoPointCorrelations.mrt_mixed_real_bin_separation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:23.965658+00:00
-- url     : https://prove2.me/theorems/23b100dd-6ebd-4547-b0ad-46d44bdfdace
-- title:
--   An explicit inequality between the amplification cost of two Matomäki–Radziwiłł scales
-- statement:
--   Let $\eta\in[0,1/6]$, $j\in\mathbb N$, and reals $Y>1$, $u>0$, $\tau\ge0$ with $\log Y\ge1$, $\log\lceil Y\rceil\le\log u$, $32(j+2)^2(\log\log u+1)\le\eta\log Y$ and $8(j+2)^2(\log Y+\log2)\le\eta\log u$. Let $\alpha_i=\frac14-\eta\big(1+\frac1{2(i+1)}\big)$ (`mrtFrequencyExponent η i`) and $a=\lceil\log u/\log\lceil Y\rceil\rceil$ (`mrtAmplificationOrder ⌈Y⌉ u`). Then
--
--   $$\frac{e^{-2\alpha_{j+1}\log u}\,\big(\tau+2^{a+1}\lceil Y\rceil\big)\,(a!)^2}{\big(e^{-\alpha_j\log Y}\big)^{2a}}\le(\tau+1)\exp\Big(-\frac{\eta\log u}{2(j+2)^2}\Big).$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_mixed_real_bin_separation`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations


theorem mrt_mixed_real_bin_separation {η Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ) (hY : 1 < Y)
    (hlogY : 1 ≤ Real.log Y)
    (hYu : Real.log (⌈Y⌉₊ : ℝ) ≤ Real.log u) (hu0 : 0 < u) (hτ : 0 ≤ τ)
    (hsep : 32 * ((j : ℝ) + 2) ^ 2 * (Real.log (Real.log u) + 1) ≤
      η * Real.log Y)
    (hsize : 8 * ((j : ℝ) + 2) ^ 2 * (Real.log Y + Real.log 2) ≤
      η * Real.log u) :
    Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) *
        (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2 /
        Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
          (2 * mrtAmplificationOrder ⌈Y⌉₊ u) ≤
      (τ + 1) * Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  sorry

end OAI.TwoPointCorrelations
