-- Prove2me | Theorems.Thm_OAI_SK_Analytic_pairMismatch_pressure_gap
-- name    : OAI.SK.Analytic.pairMismatch_pressure_gap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:59:20.497295+00:00
-- url     : https://prove2.me/theorems/55d01cb1-5557-4cde-90ac-c5bb2f55ec0a
-- title:
--   OAI.SK.Analytic.pairMismatch_pressure_gap: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.pairMismatch_pressure_gap` of [lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/PairGibbsGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/PairGibbsGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`):
--
--   ```lean
--   theorem pairMismatch_pressure_gap {n : ℕ} (hn : 0<n) (β : ℝ)
--       (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
--       (hmin : scalarCDFParisi β α=finiteParisiInf β)
--       {e : ℝ} (he : 0≤e) {s : ReplicaConfig n 2} (hs : s∈pairMismatchSet n β α e) :
--       matrixConstrainedPressure n 2 β (replicaGram s)≤2*finiteParisiInf β-e^2/2
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.ReplicaConfig` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.replicaGram` (definitions bundle `OAIQ036S002` of this split); `OAI.SK.Analytic.matrixConstrainedPressure` (definitions bundle `OAIQ036S003` of this split); `OAI.SK.Analytic.finiteParisiInf`, `OAI.SK.Analytic.pairMismatchSet` and `OAI.SK.Analytic.scalarCDFParisi` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proofs of `OAI.SK.Analytic.signed_small_scale` and `OAI.SK.main` of this split import it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/PairGibbsGap.lean (declaration OAI.SK.Analytic.pairMismatch_pressure_gap)

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
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem pairMismatch_pressure_gap {n : ℕ} (hn : 0<n) (β : ℝ)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hmin : scalarCDFParisi β α=finiteParisiInf β)
    {e : ℝ} (he : 0≤e) {s : ReplicaConfig n 2} (hs : s∈pairMismatchSet n β α e) :
    matrixConstrainedPressure n 2 β (replicaGram s)≤2*finiteParisiInf β-e^2/2 := by
  sorry

end SK.Analytic

end
end

end OAI
end
