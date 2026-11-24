-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_finrank_map_le_of_ker
-- name    : GlobalTheory.CompanionTheory.CommNil.finrank_map_le_of_ker
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:46.616264+00:00
-- url     : https://prove2.me/theorems/59dd7435-d684-499f-b693-49d3a99acc11
-- title:
--   Comm Nil: finrank map le of ker
-- statement:
--   The Comm Nil construction uses the finrank map le of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FinrankRangePowConvex.lean#L100-L109

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

theorem GlobalTheory.CompanionTheory.CommNil.finrank_map_le_of_ker {E F G : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
    (f : E →ₗ[ℂ] F) (T : E →ₗ[ℂ] G) (A : Submodule ℂ E)
    (h : ∀ b ∈ A, T b = 0 → f b = 0) : finrank ℂ (A.map f) ≤ finrank ℂ (A.map T) := by sorry
