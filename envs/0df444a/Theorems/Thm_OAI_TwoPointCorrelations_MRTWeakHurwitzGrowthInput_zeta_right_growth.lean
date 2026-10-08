-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_zeta_right_growth
-- name    : OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.zeta_right_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:12.488876+00:00
-- url     : https://prove2.me/theorems/a9111948-0caa-444c-8a17-e3c6011a166f
-- title:
--   Under the weak Hurwitz growth input, |ζ′/ζ(σ+it)| ≤ C log²(2|t|+3) for σ > 1
-- statement:
--   Assume `MRTWeakHurwitzGrowthInput`. Then there are $C,T>0$ such that for all reals $\sigma>1$ and $|t|\ge T$,
--
--   $$\Big|\frac{\zeta'(\sigma+it)}{\zeta(\sigma+it)}\Big|\le C\log(|2t|+3)^2.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.zeta_right_growth`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open scoped Topology

theorem MRTWeakHurwitzGrowthInput.zeta_right_growth (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ σ t : ℝ, T ≤ |t| → 1 < σ →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (mrtVKLog (2 * t)) ^ 2 := by
  sorry

end OAI.TwoPointCorrelations
