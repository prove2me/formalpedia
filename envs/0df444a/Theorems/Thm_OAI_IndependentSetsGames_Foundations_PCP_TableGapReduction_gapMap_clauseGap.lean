-- Prove2me | Theorems.Thm_OAI_IndependentSetsGames_Foundations_PCP_TableGapReduction_gapMap_clauseGap
-- name    : OAI.IndependentSetsGames.Foundations.PCP.TableGapReduction.gapMap_clauseGap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:02:45.651139+00:00
-- url     : https://prove2.me/theorems/56e5d025-d1bc-4ded-879c-bce961ae3e56
-- title:
--   OAI.IndependentSetsGames.Foundations.PCP.TableGapReduction.gapMap_clauseGap: intermediate lemma from OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LargeIndependentSets.mainTheoremReal`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Hardness of finding large independent sets in three-colorable graphs (result family 106)*, OpenAI Math Release, September 24, 2026, result family 106, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IndependentSetsGames.Foundations.PCP.TableGapReduction.gapMap_clauseGap` of [lean/OAI/Combinatorics/IndependentSets/PCP/RoundTableGap.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/PCP/RoundTableGap.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IndependentSetsGames.Foundations.PCP.TableGapReduction`, with `open RoundTables TableIteration SpectralReturn Target`):
--
--   ```lean
--   theorem gapMap_clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
--       Hastad.SourceGap.ClauseGap (gapMap H F) PCPIteration.finalClauseGap
--   ```
--
--   **Definitions.** The statement is written with `OAI.IndependentSetsGames.Foundations.Target.Formula` (definitions bundle `OAIQ069A000` of this split); `OAI.IndependentSetsGames.Foundations.PCP.Expanders.baseDegree` (definitions bundle `OAIQ069A001` of this split); `OAI.IndependentSetsGames.Foundations.PCP.ExpanderTables.graph` and `OAI.IndependentSetsGames.Foundations.PCP.RoundTables.BaseTable` (definitions bundle `OAIQ069A003` of this split); `OAI.IndependentSetsGames.Foundations.Hastad.SourceGap.ClauseGap`, `OAI.IndependentSetsGames.Foundations.PCP.PCPIteration.finalClauseGap`, `OAI.IndependentSetsGames.Foundations.PCP.SpectralReturn.SpectralCertificate` and `OAI.IndependentSetsGames.Foundations.Target.Formula.Satisfiable` (definitions bundle `OAIQ069A004` of this split); `OAI.IndependentSetsGames.Foundations.PCP.TableIteration.gapMap` (definitions bundle `OAIQ069A007` of this split).
--
--   **Used by.** The proof of `OAI.LargeIndependentSets.mainTheoremReal` of this split imports it.
-- source:
--   OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 106; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/IndependentSets/PCP/RoundTableGap.lean (declaration OAI.IndependentSetsGames.Foundations.PCP.TableGapReduction.gapMap_clauseGap)

import Mathlib
import Definitions.Def_OAIQ069A007

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem gapMap_clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (gapMap H F) PCPIteration.finalClauseGap := by
  sorry

end IndependentSetsGames.Foundations.PCP.TableGapReduction

end OAI
end
