-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalHensel_stHensel_holds
-- name    : GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:52:09.064949+00:00
-- url     : https://prove2.me/theorems/49dc4ffa-911f-42f1-854c-7cc45533c5a1
-- title:
--   Local Hensel: st Hensel holds
-- statement:
--   The Local Hensel construction uses the st Hensel holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HenselStatement.lean#L8-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HenselStatement.lean#L8-L44

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HenselStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalHensel

theorem GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds : StHensel := by sorry
