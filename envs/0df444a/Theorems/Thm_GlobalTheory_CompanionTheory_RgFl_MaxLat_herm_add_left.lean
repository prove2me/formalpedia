-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_herm_add_left
-- name    : GlobalTheory.CompanionTheory.RgFl.MaxLat.herm_add_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:35.468259+00:00
-- url     : https://prove2.me/theorems/0b04d97b-b35e-467a-b922-455bd370230c
-- title:
--   Max Lat: herm add left
-- statement:
--   The Max Lat construction uses the herm add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L13-L15

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

theorem GlobalTheory.CompanionTheory.RgFl.MaxLat.herm_add_left {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (x y z : V) :
    h (x + y) z = h x z + h y z := by sorry
