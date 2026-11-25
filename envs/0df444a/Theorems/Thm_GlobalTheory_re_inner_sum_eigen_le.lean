-- Prove2me | Theorems.Thm_GlobalTheory_re_inner_sum_eigen_le
-- name    : GlobalTheory.re_inner_sum_eigen_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:49.017732+00:00
-- url     : https://prove2.me/theorems/65d5b9c6-c326-490e-8c2b-428343314e6c
-- title:
--   Global Theory: re inner sum eigen le
-- statement:
--   The Global Theory construction uses the re inner sum eigen le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ReInnerLeOnImageOfIntertwining.lean#L8-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ReInnerLeOnImageOfIntertwining.lean#L8-L37

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

theorem GlobalTheory.re_inner_sum_eigen_le {N ι : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    [Fintype ι] (B : N →ₗ[ℂ] N) (hB : B.IsSymmetric) (C : ℝ) (v : ι → N) (l : ι → ℝ)
    (hv : ∀ i, B (v i) = (l i : ℂ) • v i) (hl : ∀ i, l i ≤ C) :
    (⟪∑ i, v i, B (∑ i, v i)⟫_ℂ).re ≤ C * ‖∑ i, v i‖ ^ 2 := by sorry
