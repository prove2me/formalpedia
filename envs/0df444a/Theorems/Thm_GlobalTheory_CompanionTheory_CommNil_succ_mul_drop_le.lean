-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_succ_mul_drop_le
-- name    : GlobalTheory.CompanionTheory.CommNil.succ_mul_drop_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:50.379299+00:00
-- url     : https://prove2.me/theorems/f053b6be-0f13-4846-a5b6-fca1040cebbd
-- title:
--   Comm Nil: succ mul drop le
-- statement:
--   The Comm Nil construction uses the succ mul drop le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L59-L70

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

theorem GlobalTheory.CompanionTheory.CommNil.succ_mul_drop_le [FiniteDimensional ℂ V] (a : Module.End ℂ V) (x : ℕ) :
    (x + 1) * finrank ℂ (LinearMap.range (a ^ x)) + finrank ℂ (LinearMap.range (a ^ (x + 1))) ≤
      (x + 1) * finrank ℂ (LinearMap.range (a ^ (x + 1))) +
        finrank ℂ (LinearMap.range (a ^ 0)) := by sorry
