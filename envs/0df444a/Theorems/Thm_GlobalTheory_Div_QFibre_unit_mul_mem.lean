-- Prove2me | Theorems.Thm_GlobalTheory_Div_QFibre_unit_mul_mem
-- name    : GlobalTheory.Div.QFibre.unit_mul_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:51:12.999662+00:00
-- url     : https://prove2.me/theorems/abf50be5-5f18-4e39-bb0f-7db211b772da
-- title:
--   QFibre: unit mul mem
-- statement:
--   The QFibre construction uses the unit mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivFourierClassesPosConeSummand.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivFourierClassesPosConeSummand.lean#L16-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.QFibre
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.Div.QFibre.unit_mul_mem (𝔞 : Frac F) (ε : (𝓞 F)ˣ) {x : F} (hx : x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ((ε : 𝓞 F) : F) * x ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by sorry
