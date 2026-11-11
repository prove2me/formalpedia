-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLocalAnchor_state_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:02:45.926857+00:00
-- url     : https://prove2.me/theorems/17f8f09d-4f13-41f4-b4c5-f3e520180d45
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalFuel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalFuel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor`, with `open WordOperations WordList BinaryArithmetic RationalLeaves Polynomial`, `open BinaryFiniteContext (labels setBits)`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma state_pack_s238 {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (r : ℕ) :
--       state (pack distance fs r)=BinaryLocalSearch.pack distance (fs.map original) ((fs.take r).toFinset.image original)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238K017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.pack` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state` (definitions bundle `Q238K037` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryLocalAnchor_integral_spec_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalFuel.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state_pack)

import Mathlib
import Definitions.Def_Q238K037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open WordOperations WordList BinaryArithmetic RationalLeaves Polynomial
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] Take.run BinaryLabel.sort
lemma state_pack_s238 {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (r : ℕ) :
    state (pack distance fs r)=BinaryLocalSearch.pack distance (fs.map original) ((fs.take r).toFinset.image original) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

end OAI
end
