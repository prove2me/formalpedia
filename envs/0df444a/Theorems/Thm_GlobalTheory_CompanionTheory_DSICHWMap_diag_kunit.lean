-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSICHWMap_diag_kunit
-- name    : GlobalTheory.CompanionTheory.DSICHWMap.diag_kunit
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:43.190001+00:00
-- url     : https://prove2.me/theorems/34a46d77-b48b-4003-9ed3-b2c4c39647e5
-- title:
--   DSICHWMap: diag kunit
-- statement:
--   The DSICHWMap construction uses the diag kunit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HwMapOfLowSpan.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HwMapOfLowSpan.lean#L43-L48

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HwMapOfLowSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICHWMap
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
variable {T V : Type} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem GlobalTheory.CompanionTheory.DSICHWMap.diag_kunit {n : ℕ} {ε : Fin n → Bool} {ET : Fin n → Fin n → Module.End ℂ T}
    {E : Fin n → Fin n → Module.End ℂ V} (h1 : KUnit ε ET) (h2 : KUnit ε E) :
    KUnit ε (fun a b => diagOp (ET a b) (E a b)) := by sorry
