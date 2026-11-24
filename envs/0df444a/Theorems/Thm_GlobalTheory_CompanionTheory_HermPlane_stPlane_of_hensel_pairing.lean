-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_stPlane_of_hensel_pairing
-- name    : GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:35.219429+00:00
-- url     : https://prove2.me/theorems/b04a3a45-079f-4618-9bea-04459674719f
-- title:
--   Herm Plane: st Plane of hensel pairing
-- statement:
--   The Herm Plane construction uses the st Plane of hensel pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L333-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L333-L373

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermPlane

theorem GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing : StHensel → StPairing → StPlane := by sorry
