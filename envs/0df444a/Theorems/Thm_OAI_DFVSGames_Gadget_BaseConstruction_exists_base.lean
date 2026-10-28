-- Prove2me | Theorems.Thm_OAI_DFVSGames_Gadget_BaseConstruction_exists_base
-- name    : OAI.DFVSGames.Gadget.BaseConstruction.exists_base
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:32:29.342594+00:00
-- url     : https://prove2.me/theorems/a017af9c-95fd-42f0-ab59-25c0538b3bf3
-- title:
--   OAI.DFVSGames.Gadget.BaseConstruction.exists_base: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.Gadget.BaseConstruction.exists_base` of [lean/OAI/Computability/DirectedFeedback/Probability/PolynomialProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Probability/PolynomialProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames.Gadget.BaseConstruction`, with `open Quadratic QuadraticStageNoise Harmonic Parameters`, `open scoped Classical`):
--
--   ```lean
--   theorem exists_base (p : ℚ) (hp : 0 < p) :
--       ∃ d : ℕ, 0 < d ∧ ∃ n : ℕ,
--         StageNoiseRecurrence.error (quotientStage (F := BinaryField d) n) ≤ p ∧
--         ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
--           (T : (quotientStage (F := BinaryField d) n).Input →ₗ[ZMod 2] E),
--           Function.Injective (T.comp (quotientStage (F := BinaryField d) n).embed) →
--           (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
--             if T ((quotientStage (F := BinaryField d) n).noise t) ≠ 0 then 1 else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DFVSGames.Quadratic.Vec` (definitions bundle `OAIQ085D002` of this split); `OAI.DFVSGames.Quadratic.BinaryField`, `OAI.DFVSGames.Gadget.Stage`, `OAI.DFVSGames.Gadget.StageNoiseRecurrence.average` and `OAI.DFVSGames.Gadget.StageNoiseRecurrence.error` (definitions bundle `OAIQ085D003` of this split); `OAI.DFVSGames.Quadratic.binaryFieldFintype` and `OAI.DFVSGames.Gadget.QuadraticStageNoise.quotientStage` (definitions bundle `OAIQ085D009` of this split).
--
--   **Used by.** The proof of `OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse` of this split imports it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Probability/PolynomialProbability.lean (declaration OAI.DFVSGames.Gadget.BaseConstruction.exists_base)

import Mathlib
import Definitions.Def_OAIQ085D009

section

attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.BaseConstruction

open Quadratic QuadraticStageNoise Harmonic Parameters
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

theorem exists_base (p : ℚ) (hp : 0 < p) :
    ∃ d : ℕ, 0 < d ∧ ∃ n : ℕ,
      StageNoiseRecurrence.error (quotientStage (F := BinaryField d) n) ≤ p ∧
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
        (T : (quotientStage (F := BinaryField d) n).Input →ₗ[ZMod 2] E),
        Function.Injective (T.comp (quotientStage (F := BinaryField d) n).embed) →
        (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
          if T ((quotientStage (F := BinaryField d) n).noise t) ≠ 0 then 1 else 0) := by
  sorry

end

end DFVSGames.Gadget.BaseConstruction

end OAI
end
