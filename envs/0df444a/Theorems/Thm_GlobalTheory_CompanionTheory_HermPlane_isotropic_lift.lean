-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_isotropic_lift
-- name    : GlobalTheory.CompanionTheory.HermPlane.isotropic_lift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:22.217493+00:00
-- url     : https://prove2.me/theorems/aecf40c5-b275-4f87-99d6-3b984507846c
-- title:
--   Herm Plane: isotropic lift
-- statement:
--   The Herm Plane construction uses the isotropic lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L159-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L159-L188

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

theorem GlobalTheory.CompanionTheory.HermPlane.isotropic_lift [CompleteSpace L] (hH : StHensel) {s : L →+* L} (hs : IsInv s) {δ : L}
    (hδ : IsDelta s δ) {h : V → V → L} (hh : IsHerm s h) {x y : V} {N : L} (hN0 : N ≠ 0)
    (hN1 : ‖N‖ < 1) (hNs : s N = N) (hqx : ‖h x x‖ ≤ ‖N‖) (hqy : ‖h y y‖ ≤ 1) (hxy : h x y = δ) :
    ∃ a : L, ‖a‖ ≤ ‖N‖ ∧ h (x + a • y) (x + a • y) = 0 := by sorry
