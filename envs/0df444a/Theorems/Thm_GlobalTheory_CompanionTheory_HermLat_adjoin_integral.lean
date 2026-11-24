-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_adjoin_integral
-- name    : GlobalTheory.CompanionTheory.HermLat.adjoin_integral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:51.5988+00:00
-- url     : https://prove2.me/theorems/a6e757fc-9618-4ebe-85ef-8e28c869c8a2
-- title:
--   Herm Lat: adjoin integral
-- statement:
--   The Herm Lat construction uses the adjoin integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L97-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L97-L120

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

theorem GlobalTheory.CompanionTheory.HermLat.adjoin_integral (hs : IsInv s) (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {p : L} (hp0 : p ≠ 0) {x : V}
    (hq : ‖h x x‖ ≤ ‖p‖ ^ 2) (hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖) :
    ∀ z ∈ adjoin L Λ (p⁻¹ • x), ‖h z z‖ ≤ 1 := by sorry
