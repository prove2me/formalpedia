-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_lat_commens
-- name    : GlobalTheory.CompanionTheory.HermPlane.lat_commens
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:25.96738+00:00
-- url     : https://prove2.me/theorems/63b85bf4-c7ad-40aa-9e4e-20fef51349ad
-- title:
--   Herm Plane: lat commens
-- statement:
--   The Herm Plane construction uses the lat commens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L38-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L38-L70

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

theorem GlobalTheory.CompanionTheory.HermPlane.lat_commens {Λ M : AddSubgroup V} (hΛ : IsLat L Λ) (hM : IsLat L M) {p : L} (hp0 : p ≠ 0)
    (hp1 : ‖p‖ < 1) : ∃ r : ℕ, ∀ x ∈ M, p ^ r • x ∈ Λ := by sorry
