-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_working_parameters
-- name    : OAI.TwoPointCorrelations.mrt_working_parameters
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:48.838043+00:00
-- url     : https://prove2.me/theorems/4d907558-0db7-49a8-9d22-6392a91c1b5c
-- title:
--   The Matomäki–Radziwiłł working parameters satisfy all the size conditions
-- statement:
--   There are $W_0$ and $X_0$ such that for every $W\ge W_0$, every natural $H>0$ with $\log H\ge1$ and $W\le(\log H)^5$, and every natural $X\ge X_0$ with $W\le(\log X)^{1/125}$: putting $P=W^{500000}$ and $Q=h/W^3$ with $h$ = `majorArcWorkingLength H W`,
--
--   - $2\le P\le Q$, $\log P\ge2$, $\log Q\ge1$, $8192(\log\log Q+1)\le\frac1{100}\log P$, and $W^{100}\le\mathrm{res}$, $2\le\mathrm{res}$ for $\mathrm{res}$ = `mrtBaseResolution P Q (1/100)`;
--   - $\log Q\le\frac12\sqrt{\log X}$ and $2Q\le\lceil\sqrt X\rceil$;
--   - there is $J\ge1$ with $200\log\log(4X)+1\le\log\mathrm{lo}_J$, $\frac12\sqrt{\log X}<\log\mathrm{up}_{J+1}$, $\log\mathrm{up}_i\le\frac12\sqrt{\log X}$ for $1\le i\le J$, and for every natural $n\in[\lceil\sqrt X\rceil,4X]$, $200\log\log n+1\le\log\mathrm{lo}_J$ and $\mathrm{up}_i\le\exp(\sqrt{\log n})$ for $1\le i\le J$,
--
--   where $\mathrm{lo}_j=\exp(j^{4j}(\log Q)^{j-1}\log P)$ and $\mathrm{up}_j=\exp(j^{4j+2}(\log Q)^j)$ (`mrtBandLower`, `mrtBandUpper`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_working_parameters`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset

theorem mrt_working_parameters :
    ∃ W₀ : ℝ, ∃ X₀ : ℕ, ∀ W : ℝ, W₀ ≤ W →
    ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) → W ≤ Real.log (H:ℝ)^5 →
    ∀ X : ℕ, X₀ ≤ X → W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      let P := W^(500000:ℕ)
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      (2 ≤ P ∧ P ≤ Q ∧ 2 ≤ Real.log P ∧ 1 ≤ Real.log Q ∧
        8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P ∧
        W^100 ≤ mrtBaseResolution P Q (1/100) ∧ 2 ≤ mrtBaseResolution P Q (1/100)) ∧
      (Real.log Q ≤ Real.sqrt (Real.log X)/2 ∧ 2*Q ≤ (⌈Real.sqrt (X:ℝ)⌉₊:ℝ)) ∧
      ∃ J : ℕ, 1 ≤ J ∧
        200*Real.log (Real.log (4*(X:ℝ)))+1 ≤ Real.log (mrtBandLower P Q J) ∧
        Real.sqrt (Real.log X)/2 < Real.log (mrtBandUpper Q (J+1)) ∧
        (∀ i ∈ Icc 1 J, Real.log (mrtBandUpper Q i) ≤ Real.sqrt (Real.log X)/2) ∧
        ∀ n : ℕ, ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n → n ≤ 4*X →
          200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
          ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (Real.sqrt (Real.log n)) := by
  sorry

end OAI.TwoPointCorrelations
