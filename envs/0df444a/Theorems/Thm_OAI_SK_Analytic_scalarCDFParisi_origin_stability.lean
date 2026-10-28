-- Prove2me | Theorems.Thm_OAI_SK_Analytic_scalarCDFParisi_origin_stability
-- name    : OAI.SK.Analytic.scalarCDFParisi_origin_stability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T05:01:32.382249+00:00
-- url     : https://prove2.me/theorems/87ec1ae0-59bc-4ebb-810d-b7a48e9df572
-- title:
--   OAI.SK.Analytic.scalarCDFParisi_origin_stability: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.scalarCDFParisi_origin_stability` of [lean/OAI/Probability/SKBarriers/SKBarriers/Parisi/CDFOriginStability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Parisi/CDFOriginStability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped NNReal Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`):
--
--   ```lean
--   theorem scalarCDFParisi_origin_stability {β : ℝ} (hβ : β≠0)
--       (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
--       (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
--       β^2*(scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0)^2 ≤ 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.scalarCDFHessian` (definitions bundle `OAIQ036S002` of this split); `OAI.SK.Analytic.finiteParisiInf` and `OAI.SK.Analytic.scalarCDFParisi` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.exists_scalarCDFParisi_minimizer_locking_data` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Parisi/CDFOriginStability.lean (declaration OAI.SK.Analytic.scalarCDFParisi_origin_stability)

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
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFParisi_origin_stability {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    β^2*(scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0)^2 ≤ 1 := by
  sorry

end SK.Analytic

end
end

end OAI
end
