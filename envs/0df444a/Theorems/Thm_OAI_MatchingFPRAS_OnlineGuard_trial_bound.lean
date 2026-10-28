-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_OnlineGuard_trial_bound
-- name    : OAI.MatchingFPRAS.OnlineGuard.trial_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:06:43.922296+00:00
-- url     : https://prove2.me/theorems/7129c9a1-8bdc-4e8a-8567-fb810176134e
-- title:
--   OAI.MatchingFPRAS.OnlineGuard.trial_bound: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.OnlineGuard.trial_bound` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineRunCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineRunCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.OnlineGuard`, with `open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineTrial`):
--
--   ```lean
--   lemma trial_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
--       (f : Edges→Edges) (_hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G),
--       trialRealizer.cost (OnlineTrial.initial f p)+(trial (OnlineTrial.initial f p)).worst weight≤
--         q.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.ExecutableAdaptive.GraphData`, `OAI.MatchingFPRAS.ExecutableScaling.Vector`, `OAI.MatchingFPRAS.ExecutableSource.RawLogical`, `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.ExecutableSource.StageControls`, `OAI.MatchingFPRAS.OnlineGraph.Edges` and `OAI.MatchingFPRAS.PhysicalStream.Experiment.worst` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.ExecutableAdaptive.graphRep`, `OAI.MatchingFPRAS.ExecutableSource.SparseStageData`, `OAI.MatchingFPRAS.TreeTyped.weight` and `OAI.MatchingFPRAS.Trial.Parameters` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.OnlineGraph.graph` (definitions bundle `OAIQ051M003` of this split); `OAI.MatchingFPRAS.OnlineGuard.trial`, `OAI.MatchingFPRAS.OnlineGuard.trialRealizer`, `OAI.MatchingFPRAS.OnlineSchedule.RequestInput`, `OAI.MatchingFPRAS.OnlineTrial.State`, `OAI.MatchingFPRAS.OnlineTrial.initial`, `OAI.MatchingFPRAS.OnlineTrial.sizeNorm` and `OAI.MatchingFPRAS.OnlineTree.Realizer` (definitions bundle `OAIQ051M004` of this split); `OAI.MatchingFPRAS.GraphInput` (the published bundle `Def_MatchingFPRAS`).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineRunCost.lean (declaration OAI.MatchingFPRAS.OnlineGuard.trial_bound)

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineGuard
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineTrial

lemma trial_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (f : Edges→Edges) (_hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G),
    trialRealizer.cost (OnlineTrial.initial f p)+(trial (OnlineTrial.initial f p)).worst weight≤
      q.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  sorry
end MatchingFPRAS.OnlineGuard

end OAI
end
