-- Prove2me | Theorems.Thm_OAI_DFVSGames_Decoder_ActualProjectedTransfer_actual_success_lower
-- name    : OAI.DFVSGames.Decoder.ActualProjectedTransfer.actual_success_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:45:46.90531+00:00
-- url     : https://prove2.me/theorems/becea0df-de16-4593-906d-125b3ba0e5ef
-- title:
--   OAI.DFVSGames.Decoder.ActualProjectedTransfer.actual_success_lower: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.Decoder.ActualProjectedTransfer.actual_success_lower` of [lean/OAI/Computability/DirectedFeedback/Games/VisibleTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/VisibleTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames.Decoder.ActualProjectedTransfer`, with `open Integration.BinaryLinear Reduction ActualSource Foundations.Games`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem actual_success_lower (S : Source)
--       (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
--       (α g₀ β : ℝ) (hα : 0 < α)
--       (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
--       (hβ : 0 ≤ β) (hβ' : β ≤ 1)
--       (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
--       (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
--       ConstantSelection.decodingMass α g₀ s r ≤
--         (ActualSeedEvents.law S k s d r β hβ hβ').expectation
--           (fun seed => VisiblePolicies.observedAgreement S labeling
--             (SelectedPolicies.goodPredicate S labeling α hα hsmall)
--             (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DFVSGames.Decoder.AdviceLaw.ProjectionSeed`, `OAI.DFVSGames.Decoder.PaddedLaw.ProjectionChoice`, `OAI.DFVSGames.Decoder.PaddedLaw.choiceMask`, `OAI.DFVSGames.Decoder.TableKeysGame.vertexCount`, `OAI.DFVSGames.Integration.BinaryLinear.F2`, `OAI.DFVSGames.Integration.BinaryLinear.Vector`, `OAI.DFVSGames.Reduction.ActualSource.Alphabet`, `OAI.DFVSGames.Reduction.ActualSource.Source`, `OAI.DFVSGames.Soundness.ConditionalIncidences.RawSlot` and `OAI.DFVSGames.Soundness.RawPartnerTarget.RawPoint` (definitions bundle `OAIQ085D000` of this split); `OAI.DFVSGames.Decoder.ConstantSelection.decodingMass` and `OAI.DFVSGames.Decoder.ConstantSelection.variationBudget` (definitions bundle `OAIQ085D001` of this split); `OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype`, `OAI.DFVSGames.Decoder.AdviceLaw.seedToActualDraw`, `OAI.DFVSGames.Decoder.VisiblePolicies.observedAgreement`, `OAI.DFVSGames.Soundness.RawMapLaw.rawMapsFintype` and `OAI.DFVSGames.Foundations.Games.FiniteDistribution.expectation` (definitions bundle `OAIQ085D007` of this split); `OAI.DFVSGames.Decoder.ActualSeedEvents.Seed` (definitions bundle `OAIQ085D018` of this split); `OAI.DFVSGames.Decoder.ActualGoodRows.adviceMass`, `OAI.DFVSGames.Decoder.ActualProjectedTransfer.slopeVariation`, `OAI.DFVSGames.Decoder.ActualSeedEvents.law` and `OAI.DFVSGames.Decoder.SelectedPolicies.goodPredicate` (definitions bundle `OAIQ085D024` of this split).
--
--   **Used by.** The proof of `OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction` of this split imports it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/VisibleTransfer.lean (declaration OAI.DFVSGames.Decoder.ActualProjectedTransfer.actual_success_lower)

import Mathlib
import Definitions.Def_OAIQ085D024

section

attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualProjectedTransfer

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_re0f0e0_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
theorem actual_success_lower (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : slopeVariation k s d β ≤ ConstantSelection.variationBudget α g₀ s r) :
    ConstantSelection.decodingMass α g₀ s r ≤
      (ActualSeedEvents.law S k s d r β hβ hβ').expectation
        (fun seed => VisiblePolicies.observedAgreement S labeling
          (SelectedPolicies.goodPredicate S labeling α hα hsmall)
          (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) := by
  sorry

end
end DFVSGames.Decoder.ActualProjectedTransfer

end OAI
end
