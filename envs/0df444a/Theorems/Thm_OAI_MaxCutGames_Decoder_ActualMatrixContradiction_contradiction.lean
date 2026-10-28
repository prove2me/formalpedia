-- Prove2me | Theorems.Thm_OAI_MaxCutGames_Decoder_ActualMatrixContradiction_contradiction
-- name    : OAI.MaxCutGames.Decoder.ActualMatrixContradiction.contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:47:40.135019+00:00
-- url     : https://prove2.me/theorems/205efe74-061b-44cd-8a67-37be00fc4883
-- title:
--   OAI.MaxCutGames.Decoder.ActualMatrixContradiction.contradiction: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaxCutGames.Decoder.ActualMatrixContradiction.contradiction` of [lean/OAI/Computability/MaxCut/Encoding/ActualAdviceSampling.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/ActualAdviceSampling.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaxCutGames.Decoder.ActualMatrixContradiction`, with `open Integration.BinaryLinear Reduction ActualSource Foundations.Games`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem contradiction (S : Source)
--       (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
--       (α g₀ β : ℝ) (hα : 0 < α)
--       (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
--       (hβ : 0 ≤ β) (hβ' : β ≤ 1)
--       (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
--       (hvariation : ActualProjectedTransfer.slopeVariation k s d β ≤
--         ConstantSelection.variationBudget α g₀ s r)
--       (hrate : (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k <
--         ConstantSelection.decodingMass α g₀ s r)
--       (hdistinct : S.DistinctNames)
--       (hopt : Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
--         (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Foundations.Games.FiniteDistribution.uniform` (definitions bundle `OAIQ087A001` of this split); `OAI.MaxCutGames.Decoder.ConstantSelection.decodingMass` and `OAI.MaxCutGames.Decoder.ConstantSelection.variationBudget` (definitions bundle `OAIQ087A002` of this split); `OAI.MaxCutGames.Clean.IncidenceGap.parityValue`, `OAI.MaxCutGames.Decoder.TableKeysGame.vertexCount`, `OAI.MaxCutGames.Reduction.ActualSource.Source` and `OAI.MaxCutGames.Reduction.ActualSource.sourceIndexNonempty` (definitions bundle `OAIQ087A008` of this split); `OAI.MaxCutGames.Decoder.ActualAdviceUpper.sourceIncidence`, `OAI.MaxCutGames.Decoder.ActualGoodRows.adviceMass` and `OAI.MaxCutGames.Decoder.ActualProjectedTransfer.slopeVariation` (definitions bundle `OAIQ087A015` of this split); `OAI.MaxCutGames.Reduction.ActualSource.Source.DistinctNames` (definitions bundle `OAIQ087A016` of this split).
--
--   **Used by.** The proof of `OAI.MaxCutGames.theorem11` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/ActualAdviceSampling.lean (declaration OAI.MaxCutGames.Decoder.ActualMatrixContradiction.contradiction)

import Mathlib
import Definitions.Def_OAIQ087A015
import Definitions.Def_OAIQ087A016

section

attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.ActualMatrixContradiction

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

theorem contradiction (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : ActualProjectedTransfer.slopeVariation k s d β ≤
      ConstantSelection.variationBudget α g₀ s r)
    (hrate : (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k <
      ConstantSelection.decodingMass α g₀ s r)
    (hdistinct : S.DistinctNames)
    (hopt : Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) : False := by
  sorry

end
end MaxCutGames.Decoder.ActualMatrixContradiction

end OAI
end
