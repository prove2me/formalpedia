-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_typical_actual_working_mean
-- name    : OAI.TwoPointCorrelations.mrt_typical_actual_working_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:37.932381+00:00
-- url     : https://prove2.me/theorems/ef15068d-7ed6-4088-b85b-f3221998a880
-- title:
--   Under the two Halász inputs, the short exponential integral of typical numbers at the working parameters
-- statement:
--   Assume `HalaszPrimeSparseInput` and `HalaszHighPrimeInput`. Then there are $C>0$, $W_0$ and $X_0$ such that for all naturals $X\ge X_0$ and $10\le H\le X$ with $\log H\ge1$, $\log\log H\ge1$, and every $M\ge0$: with $W$ = `majorArcParameter (log X) H M` $=\min((\log H)^5,(\log X)^{1/125},e^{M/3})$, $h$ = `majorArcWorkingLength H W`, $P=W^{500000}$, $Q=h/W^3$, if $W\ge W_0$ then there is $J\ge1$ with $\log\mathrm{up}_j\le\frac12\sqrt{\log X}$ for $j\le J$ such that for every $Y$ with $X\le Y$ and $Y+h\le2X$, every multiplicative $F$ with $F(1)=1$ and $|F|\le1$, satisfying `MRTDistanceLowerBound F X H M`, and every real $\alpha$,
--
--   $$\int_0^Y\Big|\sum_{y<n\le y+h}G(n)e(n\alpha)\Big|dy\le C\,Y\,h\Big(e^{-M/20}+\frac{\log\log H}{\log H}+(\log X)^{-1/700}\Big),$$
--
--   where $G$ = `mrtTypicalCoefficient (Icc 1 J) (band primes) F` and the last two error terms are `mrtShortError X H`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_typical_actual_working_mean`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset

theorem mrt_typical_actual_working_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∃ X₀ : ℕ,
    ∀ X H : ℕ, X₀ ≤ X → 10 ≤ H → H ≤ X →
      1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter (Real.log X) H M
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      W₀ ≤ W → ∃ J : ℕ, 1 ≤ J ∧
        (∀ j ∈ Icc 1 J, Real.log (mrtBandUpper Q j) ≤ Real.sqrt (Real.log X)/2) ∧
      ∀ Y : ℕ, X ≤ Y → Y+h ≤ 2*X →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
        MRTDistanceLowerBound F X H M → ∀ α : ℝ,
        shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α ≤
        C*(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) := by
  sorry

end OAI.TwoPointCorrelations
