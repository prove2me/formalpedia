-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_short_exponential
-- name    : OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.short_exponential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:48.058866+00:00
-- url     : https://prove2.me/theorems/4a8771c7-e1cb-4aa1-93c5-200f2cc4177c
-- title:
--   The Matomäki–Radziwiłł short exponential-sum input from the weak Hurwitz growth input and the sparse prime input
-- statement:
--   If `MRTWeakHurwitzGrowthInput` and `HalaszPrimeSparseInput` hold, then `MRTShortExponentialInput` holds (all three are the bundle's propositions; the last is the bound $\int_0^X|\sum_{y<n\le y+H}b(n)e(n\alpha)|dy\le CHX(e^{-M/20}+\frac{\log\log H}{\log H}+(\log X)^{-1/700})$ for multiplicative $b$ bounded by $1$ satisfying `MRTDistanceLowerBound b X H M`, uniformly in $10\le H\le X$ and $\alpha$).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.short_exponential`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations


theorem MRTWeakHurwitzGrowthInput.short_exponential (h : MRTWeakHurwitzGrowthInput)
    (hprime : HalaszPrimeSparseInput) : MRTShortExponentialInput := by
  sorry

end OAI.TwoPointCorrelations
