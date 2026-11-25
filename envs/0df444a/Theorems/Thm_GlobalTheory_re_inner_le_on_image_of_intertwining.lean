-- Prove2me | Theorems.Thm_GlobalTheory_re_inner_le_on_image_of_intertwining
-- name    : GlobalTheory.re_inner_le_on_image_of_intertwining
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:52.636931+00:00
-- url     : https://prove2.me/theorems/f80583f2-7ec1-4157-891b-6ce0cfe48b24
-- title:
--   Global Theory: re inner le on image of intertwining
-- statement:
--   The Global Theory construction uses the re inner le on image of intertwining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ReInnerLeOnImageOfIntertwining.lean#L39-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ReInnerLeOnImageOfIntertwining.lean#L39-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwining
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.re_inner_le_on_image_of_intertwining :
    ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
      [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T)
      (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) →
      (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) →
      ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by sorry
