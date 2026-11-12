-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRandomizedZeroBranch_Prefix_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:05:36.542185+00:00
-- url     : https://prove2.me/theorems/854a3313-12b9-45b5-8e54-624f5ee73770
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPrefix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPrefix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix`, with `open WordOperations`):
--
--   ```lean
--   lemma run_pack_s238r {n K : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
--       (colors0 : Fin n→Fin 3) (q : ℕ) (extra : List Bool)
--       (hK : BinaryRandomizedZeroBranch.count n s.leaves.length≤K) (seed : Fin K→Bool) :
--       run (pairBits (BinaryZeroBranch.pack δ D F S Δ s colors0 q extra,List.ofFn seed))=
--         let seed':=BinaryRandomizedZeroBranch.layout n s.leaves.length (fun i=>seed (Fin.castLE hK i))
--         BinaryFinSet.encode (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1 i)) q seed'.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.ColorLabel.color` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.Bits` (definitions bundle `Q238L018` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Seed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.layout` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.output` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.pack` (definitions bundle `Q238L031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run` (definitions bundle `Q238L037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchPrefix.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix.run_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L031
import Definitions.Def_Q238L037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix
open WordOperations
lemma run_pack_s238r {n K : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors0 : Fin n→Fin 3) (q : ℕ) (extra : List Bool)
    (hK : BinaryRandomizedZeroBranch.count n s.leaves.length≤K) (seed : Fin K→Bool) :
    run (pairBits (BinaryZeroBranch.pack δ D F S Δ s colors0 q extra,List.ofFn seed))=
      let seed':=BinaryRandomizedZeroBranch.layout n s.leaves.length (fun i=>seed (Fin.castLE hK i))
      BinaryFinSet.encode (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1 i)) q seed'.2) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix

end OAI
end
