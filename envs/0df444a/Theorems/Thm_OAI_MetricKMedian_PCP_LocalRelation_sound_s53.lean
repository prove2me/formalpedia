-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_LocalRelation_sound_s53
-- name    : OAI.MetricKMedian.PCP.LocalRelation.sound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:36:41.734417+00:00
-- url     : https://prove2.me/theorems/3adc6331-8551-432d-82c1-803a6d356a00
-- title:
--   OAI.MetricKMedian.PCP.LocalRelation.sound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.LocalRelation.sound` of [lean/OAI/Combinatorics/KMedian/PCP/LocalReduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/PCP/LocalReduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.LocalRelation`, with `open Finset`, `open scoped BigOperators`):
--
--   ```lean
--   theorem sound_s53 (f : BitVector (Vars R) → Bit)
--       (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit)
--       (hR : (nearestLabel u, nearestLabel v) ∉ R) :
--       1/16 ≤ rejectionWeight R f h u v
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.Bit`, `OAI.MetricKMedian.PCP.BitVector`, `OAI.MetricKMedian.PCP.nearestLabel`, `OAI.MetricKMedian.PCP.LocalRelation.Relation` and `OAI.MetricKMedian.PCP.LocalRelation.Vars` (definitions bundle `OAIQ053K008` of this split); `OAI.MetricKMedian.PCP.LocalRelation.rejectionWeight` (definitions bundle `OAIQ053K036` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53` and `OAI.MetricKMedian.PCP.Compiler.CookProgram.initial_correct_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/PCP/LocalReduction.lean (declaration OAI.MetricKMedian.PCP.LocalRelation.sound)

import Mathlib
import Definitions.Def_OAIQ053K036

section

attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]

variable (R : Relation K) [DecidablePred (· ∈ R)]

theorem sound_s53 (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit)
    (hR : (nearestLabel u, nearestLabel v) ∉ R) :
    1/16 ≤ rejectionWeight R f h u v := by
  sorry

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPLocalReduction

end OAI
end
