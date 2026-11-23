-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_range_pow_succ
-- name    : GlobalTheory.CompanionTheory.CommNil.range_pow_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:25.597838+00:00
-- url     : https://prove2.me/theorems/78fe9645-cbc9-4b51-b81f-3419ef63f752
-- title:
--   Comm Nil: range pow succ
-- statement:
--   The Comm Nil construction uses the range pow succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L31-L33

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

theorem GlobalTheory.CompanionTheory.CommNil.range_pow_succ (a : Module.End ℂ V) (i : ℕ) :
    LinearMap.range (a ^ (i + 1)) = (LinearMap.range (a ^ i)).map a := by sorry
