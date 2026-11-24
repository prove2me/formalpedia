-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_exists_isDelta
-- name    : GlobalTheory.CompanionTheory.RgFl.exists_isDelta
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:37.776441+00:00
-- url     : https://prove2.me/theorems/2f64f493-ba23-438b-afe3-c9bc70c1fd94
-- title:
--   Rg Fl: exists is Delta
-- statement:
--   The Rg Fl construction uses the exists is Delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DeltaStatement.lean#L8-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DeltaStatement.lean#L8-L124

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DeltaStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl

theorem GlobalTheory.CompanionTheory.RgFl.exists_isDelta (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    [CharZero L] (s : L →+* L) (hs : IsInv s) : ∃ δ, IsDelta s δ := by sorry
