-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_norm_herm_le_delta
-- name    : GlobalTheory.CompanionTheory.RgFl.MaxLat.norm_herm_le_delta
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:38.898726+00:00
-- url     : https://prove2.me/theorems/cb6facbf-2d05-4b1b-a4f2-847fc638c3fd
-- title:
--   Max Lat: norm herm le delta
-- statement:
--   The Max Lat construction uses the norm herm le delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L35-L51

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.MaxLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]

theorem GlobalTheory.CompanionTheory.RgFl.MaxLat.norm_herm_le_delta {s : L →+* L} {δ : L} {h : V → V → L} (hδ : IsDelta s δ)
    (hh : IsHerm s h) {M : AddSubgroup V} (hO : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hM : ∀ x ∈ M, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ M) (hy : y ∈ M) : ‖h x y‖ ≤ ‖δ‖ := by sorry
