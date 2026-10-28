-- Prove2me | Theorems.Thm_OAI_LargeIndependentSets_LCInput_uniform_repetition
-- name    : OAI.LargeIndependentSets.LCInput.uniform_repetition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T01:52:43.804564+00:00
-- url     : https://prove2.me/theorems/e2aecf1f-0127-47f3-940d-2046078ed23c
-- title:
--   OAI.LargeIndependentSets.LCInput.uniform_repetition: intermediate lemma from OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LargeIndependentSets.mainTheoremReal`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Hardness of finding large independent sets in three-colorable graphs (result family 106)*, OpenAI Math Release, September 24, 2026, result family 106, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LargeIndependentSets.LCInput.uniform_repetition` of [lean/OAI/Combinatorics/IndependentSets/Reduction/FrameNonempty.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/Reduction/FrameNonempty.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LargeIndependentSets.LCInput`, with `open IndependentSetsGames.Foundations`, `open Target PCP Hastad.SourceContexts Hastad.SourceGame Games`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem uniform_repetition {η σ : ℚ} (hη : 0 < η) (hη1 : η ≤ 1) (hσ : 0 < σ) :
--       ∃ u : ℕ, 0 < u ∧ ∀ F : Target.Formula, Hastad.SourceGap.ClauseGap F η →
--         (labelCover F u).Sound (σ:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.IndependentSetsGames.Foundations.PCP.RandomEvent`, `OAI.IndependentSetsGames.Foundations.PCP.Slot`, `OAI.IndependentSetsGames.Foundations.Target.Clause`, `OAI.IndependentSetsGames.Foundations.Target.Formula`, `OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.ClauseContext`, `OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.J`, `OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.VariableContext` and `OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.slotFintype` (definitions bundle `OAIQ069A000` of this split); `OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.I` (definitions bundle `OAIQ069A001` of this split); `OAI.LargeIndependentSets.LabelCoverData.Sound` (definitions bundle `OAIQ069A002` of this split); `OAI.LargeIndependentSets.LCInput.labelCover` and `OAI.IndependentSetsGames.Foundations.Hastad.SourceGap.ClauseGap` (definitions bundle `OAIQ069A004` of this split).
--
--   **Used by.** The proof of `OAI.LargeIndependentSets.mainTheoremReal` of this split imports it.
-- source:
--   OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 106; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/Reduction/FrameNonempty.lean (declaration OAI.LargeIndependentSets.LCInput.uniform_repetition)

import Mathlib
import Definitions.Def_OAIQ069A004

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.LCInput
open IndependentSetsGames.Foundations
open Target PCP Hastad.SourceContexts Hastad.SourceGame Games
open scoped BigOperators Classical
noncomputable section

theorem uniform_repetition {η σ : ℚ} (hη : 0 < η) (hη1 : η ≤ 1) (hσ : 0 < σ) :
    ∃ u : ℕ, 0 < u ∧ ∀ F : Target.Formula, Hastad.SourceGap.ClauseGap F η →
      (labelCover F u).Sound (σ:ℝ) := by
  sorry

end
end LargeIndependentSets.LCInput

end OAI
end
