-- Prove2me | Theorems.Thm_OAI_SK_Analytic_quenchedPressure_quantitative_finiteInf
-- name    : OAI.SK.Analytic.quenchedPressure_quantitative_finiteInf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T05:02:37.407455+00:00
-- url     : https://prove2.me/theorems/316d05e1-5a6c-4cad-a82f-8d0912e435ed
-- title:
--   OAI.SK.Analytic.quenchedPressure_quantitative_finiteInf: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.quenchedPressure_quantitative_finiteInf` of [lean/OAI/Probability/SKBarriers/SKBarriers/Coverage/FiniteRateAsymptotic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Coverage/FiniteRateAsymptotic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem quenchedPressure_quantitative_finiteInf {β : ℝ} (hβ : 0 < β) :
--       ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
--         finiteParisiInf β-C*(N:ℝ)^(-(1:ℝ)/24) ≤ quenchedPressure β N ∧
--         quenchedPressure β N ≤ finiteParisiInf β
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.quenchedPressure` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Analytic.finiteParisiInf` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proofs of `OAI.SK.Analytic.signed_small_scale` and `OAI.SK.main` of this split import it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Coverage/FiniteRateAsymptotic.lean (declaration OAI.SK.Analytic.quenchedPressure_quantitative_finiteInf)

import Mathlib
import Definitions.Def_OAIQ036S004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem quenchedPressure_quantitative_finiteInf {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      finiteParisiInf β-C*(N:ℝ)^(-(1:ℝ)/24) ≤ quenchedPressure β N ∧
      quenchedPressure β N ≤ finiteParisiInf β := by
  sorry
end SK.Analytic

end
end

end

end OAI
end
