-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_succ_mul_finrank_map_le
-- name    : GlobalTheory.CompanionTheory.CommNil.succ_mul_finrank_map_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:54.247008+00:00
-- url     : https://prove2.me/theorems/bf170559-c0ea-4098-bf16-cbfd48e11ec5
-- title:
--   Comm Nil: succ mul finrank map le
-- statement:
--   The Comm Nil construction uses the succ mul finrank map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L111-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L111-L143

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

theorem GlobalTheory.CompanionTheory.CommNil.succ_mul_finrank_map_le :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : Module.End ℂ V),
      IsNilpotent a → ∀ (x : ℕ) (A : Submodule ℂ (Module.End ℂ V)), (∀ b ∈ A, Commute b a) →
        (x + 1) * Module.finrank ℂ (A.map (LinearMap.mulRight ℂ (a ^ x))) ≤
          Module.finrank ℂ V ^ 2 := by sorry
