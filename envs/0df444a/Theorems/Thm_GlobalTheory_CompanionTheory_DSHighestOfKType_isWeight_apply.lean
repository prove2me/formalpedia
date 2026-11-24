-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSHighestOfKType_isWeight_apply
-- name    : GlobalTheory.CompanionTheory.DSHighestOfKType.isWeight_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:21.946152+00:00
-- url     : https://prove2.me/theorems/68dee45e-ae61-4180-8987-1075a3475e84
-- title:
--   DSHighest Of KType: is Weight apply
-- statement:
--   The DSHighest Of KType construction uses the is Weight apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NotCdomAddRoot.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NotCdomAddRoot.lean#L42-L54

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NotCdomAddRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSHighestOfKType
open Formalism.REAL (GlRel KHighest IsWeight)
open PI.UpqRep (CDom root)
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSHighestOfKType.isWeight_apply {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {v : V} (hv : IsWeight E μ v) (a b : Fin n) :
    IsWeight E (μ + root a b) (E a b v) := by sorry
