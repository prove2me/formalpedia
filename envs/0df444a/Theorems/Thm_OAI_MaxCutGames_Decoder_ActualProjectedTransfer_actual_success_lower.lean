-- Prove2me | Theorems.Thm_OAI_MaxCutGames_Decoder_ActualProjectedTransfer_actual_success_lower
-- name    : OAI.MaxCutGames.Decoder.ActualProjectedTransfer.actual_success_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:52:14.317481+00:00
-- url     : https://prove2.me/theorems/3eee52e3-3dfe-4390-8851-6dd5f0a66511
-- title:
--   OAI.MaxCutGames.Decoder.ActualProjectedTransfer.actual_success_lower: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaxCutGames.Decoder.ActualProjectedTransfer.actual_success_lower` of [lean/OAI/Computability/MaxCut/Encoding/VisibleTransfer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/VisibleTransfer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaxCutGames.Decoder.ActualProjectedTransfer`, with `open Integration.BinaryLinear Reduction ActualSource Foundations.Games`, `open scoped BigOperators Classical`):
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
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Integration.BinaryLinear.F2` (definitions bundle `OAIQ087A000` of this split); `OAI.MaxCutGames.Decoder.PaddedLaw.ProjectionChoice`, `OAI.MaxCutGames.Decoder.PaddedLaw.choiceMask`, `OAI.MaxCutGames.Soundness.ConditionalIncidences.RawSlot` and `OAI.MaxCutGames.Foundations.Games.FiniteDistribution.expectation` (definitions bundle `OAIQ087A001` of this split); `OAI.MaxCutGames.Decoder.ConstantSelection.decodingMass` and `OAI.MaxCutGames.Decoder.ConstantSelection.variationBudget` (definitions bundle `OAIQ087A002` of this split); `OAI.MaxCutGames.Decoder.AdviceLaw.ProjectionSeed`, `OAI.MaxCutGames.Decoder.TableKeysGame.vertexCount`, `OAI.MaxCutGames.Integration.BinaryLinear.Vector`, `OAI.MaxCutGames.Reduction.ActualSource.Alphabet`, `OAI.MaxCutGames.Reduction.ActualSource.Source`, `OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype` and `OAI.MaxCutGames.Soundness.RawPartnerTarget.RawPoint` (definitions bundle `OAIQ087A008` of this split); `OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype`, `OAI.MaxCutGames.Decoder.ActualGoodRows.adviceMass`, `OAI.MaxCutGames.Decoder.ActualProjectedTransfer.slopeVariation`, `OAI.MaxCutGames.Decoder.ActualSeedEvents.Seed`, `OAI.MaxCutGames.Decoder.ActualSeedEvents.law`, `OAI.MaxCutGames.Decoder.AdviceLaw.seedToActualDraw` and `OAI.MaxCutGames.Decoder.VisiblePolicies.observedAgreement` (definitions bundle `OAIQ087A015` of this split); `OAI.MaxCutGames.Decoder.SelectedPolicies.goodPredicate` (definitions bundle `OAIQ087A021` of this split).
--
--   **Used by.** The proof of `OAI.MaxCutGames.Decoder.ActualMatrixContradiction.contradiction` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Encoding/VisibleTransfer.lean (declaration OAI.MaxCutGames.Decoder.ActualProjectedTransfer.actual_success_lower)

import Mathlib
import Definitions.Def_OAIQ087A021

section

attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.ActualProjectedTransfer

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_r04ee7e_1 {D F : Type*}
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
end MaxCutGames.Decoder.ActualProjectedTransfer

end OAI
end
