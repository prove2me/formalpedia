-- Prove2me | Theorems.Thm_OAI_SK_Analytic_scalarCDFJointSusceptibility_quantile_loss
-- name    : OAI.SK.Analytic.scalarCDFJointSusceptibility_quantile_loss
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T05:00:07.977996+00:00
-- url     : https://prove2.me/theorems/b78fc8c8-7ba0-4882-a986-a7a76cf11b4a
-- title:
--   OAI.SK.Analytic.scalarCDFJointSusceptibility_quantile_loss: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.scalarCDFJointSusceptibility_quantile_loss` of [lean/OAI/Probability/SKBarriers/SKBarriers/Parisi/CDFJointBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Parisi/CDFJointBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped NNReal Topology`, `open MeasureTheory ProbabilityTheory Filter Set`):
--
--   ```lean
--   theorem scalarCDFJointSusceptibility_quantile_loss {n : ℕ} (β : ℝ) (Q : Fin (n+1) → ℝ)
--       (hQ : Q∈admissibleQuantiles n) {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
--       scalarCDFJointSusceptibility β (quantileCDF n Q) r q ≤
--         scalarCDFSusceptibilitySquareAverage β (quantileCDF n Q) r-
--         quantileCDF n Q r*(β^2*(q-r))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.admissibleQuantiles`, `OAI.SK.Analytic.quantileCDF` and `OAI.SK.Analytic.scalarSusceptibilityFloor` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.scalarCDFJointSusceptibility` and `OAI.SK.Analytic.scalarCDFSusceptibilitySquareAverage` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.narrowCDFTrialCoefficient_quantitative` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Parisi/CDFJointBridge.lean (declaration OAI.SK.Analytic.scalarCDFJointSusceptibility_quantile_loss)

import Mathlib
import Definitions.Def_OAIQ036S004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFJointSusceptibility_quantile_loss {n : ℕ} (β : ℝ) (Q : Fin (n+1) → ℝ)
    (hQ : Q∈admissibleQuantiles n) {r q : ℝ} (hr : 0 ≤ r) (hrq : r≤q) (hq : q≤1) :
    scalarCDFJointSusceptibility β (quantileCDF n Q) r q ≤
      scalarCDFSusceptibilitySquareAverage β (quantileCDF n Q) r-
      quantileCDF n Q r*(β^2*(q-r))*(scalarSusceptibilityFloor (β^2) (1+2*β^2+4*(β^2)^2))^3/2 := by
  sorry

end SK.Analytic

end
end

end OAI
end
