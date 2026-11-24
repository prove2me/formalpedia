-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_norm_herm_ball_le_one
-- name    : GlobalTheory.CompanionTheory.RgFl.MaxLat.norm_herm_ball_le_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:33.007631+00:00
-- url     : https://prove2.me/theorems/369c23ba-ca39-4ebb-ba5f-b7db685f6bc9
-- title:
--   Max Lat: norm herm ball le one
-- statement:
--   The Max Lat construction uses the norm herm ball le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L117-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L117-L128

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

theorem GlobalTheory.CompanionTheory.RgFl.MaxLat.norm_herm_ball_le_one {s : L →+* L} {h : V → V → L} (hs : IsInv s) (hh : IsHerm s h)
    {m : ℕ} (b : Module.Basis (Fin m) L V) (hb : ∀ i j, ‖h (b i) (b j)‖ ≤ 1) {x : V}
    (hx : x ∈ ball b) : ‖h x x‖ ≤ 1 := by sorry
