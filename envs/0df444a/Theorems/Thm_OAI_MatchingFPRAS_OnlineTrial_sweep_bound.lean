-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_OnlineTrial_sweep_bound
-- name    : OAI.MatchingFPRAS.OnlineTrial.sweep_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:10:58.950576+00:00
-- url     : https://prove2.me/theorems/d1cba6f6-50bb-43cc-bcef-fa14b1c6e5e4
-- title:
--   OAI.MatchingFPRAS.OnlineTrial.sweep_bound: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.OnlineTrial.sweep_bound` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineHistoryCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineHistoryCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.OnlineTrial`, with `open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample`, `open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample`):
--
--   ```lean
--   lemma sweep_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
--       (f : Edges→Edges) (_hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G),
--       sweepRealizer.cost (initial f p)+(sweep (initial f p)).worst weight≤
--         q.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.ExecutableAdaptive.GraphData`, `OAI.MatchingFPRAS.ExecutableScaling.Vector`, `OAI.MatchingFPRAS.ExecutableSource.RawLogical`, `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.ExecutableSource.StageControls`, `OAI.MatchingFPRAS.OnlineGraph.Edges` and `OAI.MatchingFPRAS.PhysicalStream.Experiment.worst` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.ExecutableAdaptive.graphRep`, `OAI.MatchingFPRAS.ExecutableSource.SparseStageData`, `OAI.MatchingFPRAS.TreeTyped.weight` and `OAI.MatchingFPRAS.Trial.Parameters` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.OnlineGraph.graph` (definitions bundle `OAIQ051M003` of this split); `OAI.MatchingFPRAS.OnlineSchedule.RequestInput`, `OAI.MatchingFPRAS.OnlineTrial.State`, `OAI.MatchingFPRAS.OnlineTrial.initial`, `OAI.MatchingFPRAS.OnlineTrial.sizeNorm`, `OAI.MatchingFPRAS.OnlineTrial.sweep`, `OAI.MatchingFPRAS.OnlineTrial.sweepRealizer` and `OAI.MatchingFPRAS.OnlineTree.Realizer` (definitions bundle `OAIQ051M004` of this split); `OAI.MatchingFPRAS.GraphInput` (the published bundle `Def_MatchingFPRAS`).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.OnlineGuard.trial_bound` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineHistoryCost.lean (declaration OAI.MatchingFPRAS.OnlineTrial.sweep_bound)

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]

open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

lemma sweep_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (f : Edges→Edges) (_hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G),
    sweepRealizer.cost (initial f p)+(sweep (initial f p)).worst weight≤
      q.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  sorry
end MatchingFPRAS.OnlineTrial

end OAI
end
