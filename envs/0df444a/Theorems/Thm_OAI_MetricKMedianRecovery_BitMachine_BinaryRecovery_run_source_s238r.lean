-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_run_source_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:06:15.355705+00:00
-- url     : https://prove2.me/theorems/c8a5645d-f889-4f58-a2ce-439a007999a1
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/RecoveryCandidates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RecoveryCandidates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery`, with `open WordOperations WordList BinaryBranchTape Completion FiniteSampling`):
--
--   ```lean
--   lemma run_source_s238r (A : ℝ) : ∃ d : ℕ, ∀ {n m H : ℕ} (δ : Fin n→Fin n→ℚ)
--       (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (extra : List Bool)
--       (r0 y0 : Fin n) (N : ℕ), N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
--       (hn : n≤H) → (hm : m≤H) → (hH : 1≤H) → (hp : s.leaves.length≤H) →
--       ∀ (seed : Fin (tapeSize H)→Bool),
--       run d (pack δ D F S Δ s m extra (List.ofFn seed))=
--         BinaryFinSet.encode (result δ D F S Δ s hn hm hH hp r0 y0 seed)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.tapeSize` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.pack` (definitions bundle `Q238L031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run` (definitions bundle `Q238L037` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RecoveryCandidates.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source)

import Mathlib
import Definitions.Def_Q238L031
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape Completion FiniteSampling
variable {n m H : ℕ}
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (hn : n≤H) (hm : m≤H) (hH : 1≤H)
  (hp : s.leaves.length≤H) (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
lemma run_source_s238r (A : ℝ) : ∃ d : ℕ, ∀ {n m H : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (extra : List Bool)
    (r0 y0 : Fin n) (N : ℕ), N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
    (hn : n≤H) → (hm : m≤H) → (hH : 1≤H) → (hp : s.leaves.length≤H) →
    ∀ (seed : Fin (tapeSize H)→Bool),
    run d (pack δ D F S Δ s m extra (List.ofFn seed))=
      BinaryFinSet.encode (result δ D F S Δ s hn hm hH hp r0 y0 seed) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end
