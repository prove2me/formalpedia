-- Prove2me | Theorems.Thm_OAI_DFVSGames_Decoder_ActualMatrixContradiction_contradiction
-- name    : OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:42:19.991956+00:00
-- url     : https://prove2.me/theorems/5d3cf623-3e10-423a-821a-07960e50809d
-- title:
--   OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction` of [lean/OAI/Computability/DirectedFeedback/Games/ActualAdviceSampling.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/ActualAdviceSampling.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames.Decoder.ActualMatrixContradiction`, with `open Integration.BinaryLinear Reduction ActualSource Foundations.Games`, `open scoped BigOperators Classical`):
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
--   **Definitions.** The statement is written with `OAI.DFVSGames.Decoder.TableKeysGame.vertexCount`, `OAI.DFVSGames.Reduction.ActualSource.Source`, `OAI.DFVSGames.Reduction.ActualSource.sourceIndexNonempty` and `OAI.DFVSGames.Foundations.Games.FiniteDistribution.uniform` (definitions bundle `OAIQ085D000` of this split); `OAI.DFVSGames.Decoder.ConstantSelection.decodingMass` and `OAI.DFVSGames.Decoder.ConstantSelection.variationBudget` (definitions bundle `OAIQ085D001` of this split); `OAI.DFVSGames.Clean.IncidenceGap.parityValue`, `OAI.DFVSGames.Decoder.ActualAdviceUpper.sourceIncidence` and `OAI.DFVSGames.Reduction.ActualSource.Source.DistinctNames` (definitions bundle `OAIQ085D007` of this split); `OAI.DFVSGames.Decoder.ActualGoodRows.adviceMass` and `OAI.DFVSGames.Decoder.ActualProjectedTransfer.slopeVariation` (definitions bundle `OAIQ085D024` of this split).
--
--   **Used by.** The proof of `OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse` of this split imports it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/ActualAdviceSampling.lean (declaration OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction)

import Mathlib
import Definitions.Def_OAIQ085D024

section

attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualMatrixContradiction

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
end DFVSGames.Decoder.ActualMatrixContradiction

namespace DFVSGames.Gadget

universe u v

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

end DFVSGames.Gadget

end OAI
end
