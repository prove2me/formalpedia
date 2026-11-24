-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_plane_of_pair
-- name    : GlobalTheory.CompanionTheory.HermPlane.plane_of_pair
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:38.696214+00:00
-- url     : https://prove2.me/theorems/28f14721-214c-4ef4-8041-8642747f1d27
-- title:
--   Herm Plane: plane of pair
-- statement:
--   The Herm Plane construction uses the plane of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L303-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L303-L329

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
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L]
  {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]

theorem GlobalTheory.CompanionTheory.HermPlane.plane_of_pair {s : L →+* L} (hs : IsInv s) {δ : L} (hδ : IsDelta s δ) {h : V → V → L}
    (hh : IsHerm s h) {Λ M : AddSubgroup V} (hΛ : IsMax h Λ) (hM : IsMax h M) {p : L} (hp0 : p ≠ 0)
    (hp1 : ‖p‖ < 1) {r : ℕ} (hrM : ∀ y ∈ Λ, p ^ r • y ∈ M) {e y : V} (heΛ : e ∈ Λ) (hyΛ : y ∈ Λ)
    (he : h e e = 0) (hey : ‖h e y‖ = ‖δ‖) (heM : (p ^ r)⁻¹ • e ∈ M) :
    ∃ (e f : V) (u : L), u ≠ 0 ∧ h e e = 0 ∧ h f f = 0 ∧ h e f = δ ∧
      e ∈ Λ ∧ f ∈ Λ ∧ u • e ∈ M ∧ (s u)⁻¹ • f ∈ M := by sorry
