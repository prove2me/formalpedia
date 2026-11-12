-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRandomizedBranch_source_run_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:05:29.805973+00:00
-- url     : https://prove2.me/theorems/81623ff8-b1e4-4d95-8184-1776b01f2c4d
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/ObservableCapacity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/ObservableCapacity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch`, with `open WordOperations WordList BinaryBranchContext BinaryObservableBranch`):
--
--   ```lean
--   lemma source_run_s238r (A : ℝ) : ∃ d : ℕ, ∀ {n b : ℕ} (δ : Fin n→Fin n→ℚ)
--       (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (colors0 : Fin n→Fin 3)
--       (label0 : Fin n→Fin b) (q c : ℕ) (extra : List Bool) (r0 y0 : Fin n) (N : ℕ),
--       N≤extra.length → (b:ℝ)≤A*Real.log ((N:ℝ)+2) → (hb0 : 0<b) →
--       ∀ seed : BinaryBranchTape.Seed n b s.leaves.length,
--       run d (pairBits (pack δ D F S Δ s colors0 label0 q c extra,BinaryBranchTape.raw seed))=
--       BinaryFinSet.encode (output δ D F S Δ s (fun i=>ColorLabel.color (seed.1.1 i))
--         (fun i=>ColorLabel.label b hb0 (seed.1.2 i)) q c r0 y0 seed.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.ColorLabel.color`, `OAI.MetricKMedianRecovery.ColorLabel.label` and `OAI.MetricKMedianRecovery.ColorLabel.labelRange` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Seed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.Bits` and `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.output` (definitions bundle `Q238L018` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.run` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/ObservableCapacity.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch
open WordOperations WordList BinaryBranchContext BinaryObservableBranch
lemma source_run_s238r (A : ℝ) : ∃ d : ℕ, ∀ {n b : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (colors0 : Fin n→Fin 3)
    (label0 : Fin n→Fin b) (q c : ℕ) (extra : List Bool) (r0 y0 : Fin n) (N : ℕ),
    N≤extra.length → (b:ℝ)≤A*Real.log ((N:ℝ)+2) → (hb0 : 0<b) →
    ∀ seed : BinaryBranchTape.Seed n b s.leaves.length,
    run d (pairBits (pack δ D F S Δ s colors0 label0 q c extra,BinaryBranchTape.raw seed))=
    BinaryFinSet.encode (output δ D F S Δ s (fun i=>ColorLabel.color (seed.1.1 i))
      (fun i=>ColorLabel.label b hb0 (seed.1.2 i)) q c r0 y0 seed.2) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch

end OAI
end
