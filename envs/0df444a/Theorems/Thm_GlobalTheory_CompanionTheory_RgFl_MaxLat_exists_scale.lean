-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_exists_scale
-- name    : GlobalTheory.CompanionTheory.RgFl.MaxLat.exists_scale
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:35.187569+00:00
-- url     : https://prove2.me/theorems/a2675a25-cd44-486d-9633-8fb0fa5463df
-- title:
--   Max Lat: exists scale
-- statement:
--   The Max Lat construction uses the exists scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L130-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L130-L169

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

theorem GlobalTheory.CompanionTheory.RgFl.MaxLat.exists_scale {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (B : ℝ) (hB : 0 ≤ B)
    {m : ℕ} (b : Module.Basis (Fin m) L V) :
    ∃ c : L, c ≠ 0 ∧ ∀ x, (∀ j, ‖h (b j) x‖ ≤ B) → c • x ∈ ball b := by sorry
