-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_exists_pair
-- name    : GlobalTheory.CompanionTheory.HermPlane.exists_pair
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:48:07.591125+00:00
-- url     : https://prove2.me/theorems/29af06ef-fe33-436f-91d1-c3ef1c564c69
-- title:
--   Herm Plane: exists pair
-- statement:
--   The Herm Plane construction uses the exists pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L232-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L232-L301

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

theorem GlobalTheory.CompanionTheory.HermPlane.exists_pair (hH : StHensel) (hP : StPairing) {s : L →+* L} (hs : IsInv s) {δ : L}
    (hδ : IsDelta s δ) {h : V → V → L} (hh : IsHerm s h) (hiso : ∃ x, x ≠ 0 ∧ h x x = 0)
    {Λ M : AddSubgroup V} (hΛ : IsMax h Λ) (hM : IsMax h M) {p : L} (hp0 : p ≠ 0) (hp1 : ‖p‖ < 1)
    (hpm : ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖) {r : ℕ} (hr : ∀ x ∈ M, p ^ r • x ∈ Λ)
    (hmin : ∀ k < r, ∃ z ∈ M, p ^ k • z ∉ Λ) (hrM : ∀ y ∈ Λ, p ^ r • y ∈ M) :
    ∃ e y : V, e ∈ Λ ∧ y ∈ Λ ∧ h e e = 0 ∧ ‖h e y‖ = ‖δ‖ ∧ (p ^ r)⁻¹ • e ∈ M := by sorry
