-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_finrank_range_pow_convex
-- name    : GlobalTheory.CompanionTheory.CommNil.finrank_range_pow_convex
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:51.633841+00:00
-- url     : https://prove2.me/theorems/6bf619d8-13b8-4286-ad35-f12241a4fd4a
-- title:
--   Comm Nil: finrank range pow convex
-- statement:
--   The Comm Nil construction uses the finrank range pow convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L40-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L40-L57

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

theorem GlobalTheory.CompanionTheory.CommNil.finrank_range_pow_convex [FiniteDimensional ℂ V] (a : Module.End ℂ V) (i : ℕ) :
    2 * finrank ℂ (LinearMap.range (a ^ (i + 1))) ≤
      finrank ℂ (LinearMap.range (a ^ i)) + finrank ℂ (LinearMap.range (a ^ (i + 2))) := by sorry
