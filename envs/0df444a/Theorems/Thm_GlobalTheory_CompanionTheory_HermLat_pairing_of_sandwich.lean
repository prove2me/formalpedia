-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_pairing_of_sandwich
-- name    : GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:59.517288+00:00
-- url     : https://prove2.me/theorems/72992859-790f-4acd-aa96-e2f48eaf01e0
-- title:
--   Herm Lat: pairing of sandwich
-- statement:
--   The Herm Lat construction uses the pairing of sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L122-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L122-L175

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}

theorem GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich : StSandwich → StPairing := by sorry
