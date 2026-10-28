-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_clippedSiteInsertion_rate_bound_sat
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion_rate_bound_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:20:51.679061+00:00
-- url     : https://prove2.me/theorems/e8ab94a5-03ce-47c2-b825-ad462ad66687
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion_rate_bound_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion_rate_bound` of [lean/OAI/Probability/DilutedSpin/ClippedProxyRate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ClippedProxyRate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling`, `open scoped NNReal BigOperators`):
--
--   ```lean
--   lemma clippedSiteInsertion_rate_bound_sat (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
--       (u : Spec L×ℕ → ℝ) (r t : ℝ≥0) :
--       |clippedSiteInsertion M C H N L u r-clippedSiteInsertion M C H N L u t|≤
--         C*|(r:ℝ)-t|+4*(scoreRate N:ℝ)/(N+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Model` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.scoreRate`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec` and `OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ClippedProxyRate.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion_rate_bound)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {N L q : ℕ} [NeZero N]

lemma clippedSiteInsertion_rate_bound_sat (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r t : ℝ≥0) :
    |clippedSiteInsertion M C H N L u r-clippedSiteInsertion M C H N L u t|≤
      C*|(r:ℝ)-t|+4*(scoreRate N:ℝ)/(N+1) := by
  sorry

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end
