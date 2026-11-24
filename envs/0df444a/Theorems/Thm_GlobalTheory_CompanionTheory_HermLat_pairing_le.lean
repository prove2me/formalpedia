-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_pairing_le
-- name    : GlobalTheory.CompanionTheory.HermLat.pairing_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:48:02.340923+00:00
-- url     : https://prove2.me/theorems/176e37cd-09c0-43b5-b2a0-a3f3f44c65d3
-- title:
--   Herm Lat: pairing le
-- statement:
--   The Herm Lat construction uses the pairing le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L84-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PairingOfSandwichStatement.lean#L84-L95

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

theorem GlobalTheory.CompanionTheory.HermLat.pairing_le (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hL : IsLat L Λ) (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ‖h x y‖ ≤ ‖δ‖ := by sorry
