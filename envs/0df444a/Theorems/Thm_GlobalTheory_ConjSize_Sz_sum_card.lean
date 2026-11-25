-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Sz_sum_card
-- name    : GlobalTheory.ConjSize.Sz.sum_card
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:19.209668+00:00
-- url     : https://prove2.me/theorems/0b2ea4b6-0106-469e-b148-5fb2fb4ba29a
-- title:
--   Sz: sum card
-- statement:
--   The Sz construction uses the sum card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L53-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open GlobalTheory GlobalTheory.ConjSize
variable {K : Type} [Field K] (ι τ : K →+* ℂ)
variable {ι τ}

theorem GlobalTheory.ConjSize.Sz.sum_card {α : Type*} (s : Finset α) {f : α → ℂ} {B : ℝ} (h : ∀ i ∈ s, Sz ι τ (f i) B) :
    Sz ι τ (∑ i ∈ s, f i) (s.card * B) := by sorry
