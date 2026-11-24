-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_stFrame_of
-- name    : GlobalTheory.CompanionTheory.HermFrame.stFrame_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:48:01.801991+00:00
-- url     : https://prove2.me/theorems/21d09307-666b-4a64-a7b0-dd69be1cea80
-- title:
--   Herm Frame: st Frame of
-- statement:
--   The Herm Frame construction uses the st Frame of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FrameOfAnisotropicPlaneSplitting.lean#L207-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FrameOfAnisotropicPlaneSplitting.lean#L207-L209

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermFrame

theorem GlobalTheory.CompanionTheory.HermFrame.stFrame_of : StAniso → StPlane → StSplit → StFrame := by sorry
