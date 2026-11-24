-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_herm_symm_zero
-- name    : GlobalTheory.CompanionTheory.HermFrame.herm_symm_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:55.122428+00:00
-- url     : https://prove2.me/theorems/d167afd2-4338-4a7a-930e-23f6984da7df
-- title:
--   Herm Frame: herm symm zero
-- statement:
--   The Herm Frame construction uses the herm symm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FrameOfAnisotropicPlaneSplitting.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FrameOfAnisotropicPlaneSplitting.lean#L19-L20

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
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem GlobalTheory.CompanionTheory.HermFrame.herm_symm_zero (hh : IsHerm s h) {x y : V} (hxy : h x y = 0) : h y x = 0 := by sorry
