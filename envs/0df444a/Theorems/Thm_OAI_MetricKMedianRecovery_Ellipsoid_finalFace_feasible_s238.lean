-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_finalFace_feasible_s238
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:20:05.391307+00:00
-- url     : https://prove2.me/theorems/82b93842-9223-4aec-aa01-ebe1442d247d
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoordinateRow.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoordinateRow.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix RationalLinearFeasibility PolytopeCertificate`, `open scoped BigOperators`):
--
--   ```lean
--   lemma finalFace_feasible_s238 {n : ℕ} (rows : List (Row n)) (B : ℕ)
--       (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
--       ∃ x, Face (withBox rows B) (finalFace rows B) B x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.finalFace` and `OAI.MetricKMedianRecovery.Ellipsoid.withBox` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.Face` and `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row.RealHolds` (definitions bundle `Q238K015` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRawOpening_run_pack_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq_s238`, `OAI_MetricKMedianRecovery_RationalLinearFeasibility_storedForms_complete_s238` and `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoordinateRow.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible)

import Mathlib
import Definitions.Def_Q238K014
import Definitions.Def_Q238K015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

lemma finalFace_feasible_s238 {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    ∃ x, Face (withBox rows B) (finalFace rows B) B x := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
