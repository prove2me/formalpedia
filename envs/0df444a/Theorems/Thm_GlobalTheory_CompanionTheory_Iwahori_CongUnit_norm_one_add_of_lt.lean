-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_CongUnit_norm_one_add_of_lt
-- name    : GlobalTheory.CompanionTheory.Iwahori.CongUnit.norm_one_add_of_lt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:47.871702+00:00
-- url     : https://prove2.me/theorems/78229f43-75b6-4997-bc3f-c91607d40222
-- title:
--   Cong Unit: norm one add of lt
-- statement:
--   The Cong Unit construction uses the norm one add of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceEndomorphismInverseExists.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceEndomorphismInverseExists.lean#L12-L15

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceEndomorphismInverseExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.CongUnit
variable {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
  [Module L V]

theorem GlobalTheory.CompanionTheory.Iwahori.CongUnit.norm_one_add_of_lt {t : L} (ht : ‖t‖ < 1) : ‖1 + t‖ = 1 := by sorry
