-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_lat_primitive
-- name    : GlobalTheory.CompanionTheory.HermPlane.lat_primitive
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:36.346643+00:00
-- url     : https://prove2.me/theorems/e5ec3054-f8ba-4e63-923b-a119d0466dba
-- title:
--   Herm Plane: lat primitive
-- statement:
--   The Herm Plane construction uses the lat primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L72-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L72-L128

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
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]

theorem GlobalTheory.CompanionTheory.HermPlane.lat_primitive {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {p : L} (hp0 : p ≠ 0) (hp1 : ‖p‖ < 1)
    {v : V} (hv : v ≠ 0) : ∃ a : L, a ≠ 0 ∧ a • v ∈ Λ ∧ p⁻¹ • a • v ∉ Λ := by sorry
