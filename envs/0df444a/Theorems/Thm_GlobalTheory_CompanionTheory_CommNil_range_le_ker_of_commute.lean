-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_range_le_ker_of_commute
-- name    : GlobalTheory.CompanionTheory.CommNil.range_le_ker_of_commute
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:03.276202+00:00
-- url     : https://prove2.me/theorems/54f0558e-4c77-463d-82d8-97b1998ef225
-- title:
--   Comm Nil: range le ker of commute
-- statement:
--   The Comm Nil construction uses the range le ker of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L72-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L72-L98

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommNil
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.CommNil.range_le_ker_of_commute (a b : Module.End ℂ V) (hab : Commute b a) (ha : IsNilpotent a)
    (x : ℕ) (Y : Submodule ℂ V) (hY : Y ⊔ LinearMap.range (a ^ (x + 1)) = LinearMap.range (a ^ x))
    (hb : Y ≤ LinearMap.ker b) : LinearMap.range (a ^ x) ≤ LinearMap.ker b := by sorry
