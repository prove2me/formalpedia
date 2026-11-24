-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_exists_smul_mem_of_isLat
-- name    : GlobalTheory.CompanionTheory.HermLat.exists_smul_mem_of_isLat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:56.728374+00:00
-- url     : https://prove2.me/theorems/805efaa1-a0d8-4827-870a-30f94e296215
-- title:
--   Herm Lat: exists smul mem of is Lat
-- statement:
--   The Herm Lat construction uses the exists smul mem of is Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L22-L36

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
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

theorem GlobalTheory.CompanionTheory.HermLat.exists_smul_mem_of_isLat {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (v : V) :
    ∃ a : L, a ≠ 0 ∧ a • v ∈ Λ := by sorry
