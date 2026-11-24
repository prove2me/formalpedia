-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_isLat_pull
-- name    : GlobalTheory.CompanionTheory.FlDecomp.isLat_pull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:41:36.584643+00:00
-- url     : https://prove2.me/theorems/8e33901f-f290-40e8-a06a-ceecd6bd9aaf
-- title:
--   Fl Decomp: is Lat pull
-- statement:
--   The Fl Decomp construction uses the is Lat pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfFrameWittTorus.lean#L119-L123

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem GlobalTheory.CompanionTheory.FlDecomp.isLat_pull (k : V ≃ₗ[L] V) {Λ : AddSubgroup V} (hΛ : IsLat L Λ) : IsLat L (pull k Λ) := by sorry
