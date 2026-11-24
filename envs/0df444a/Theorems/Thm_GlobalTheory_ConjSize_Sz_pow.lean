-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Sz_pow
-- name    : GlobalTheory.ConjSize.Sz.pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:58.617+00:00
-- url     : https://prove2.me/theorems/7710fb6b-6b8d-4f67-83bf-66c26a8b1371
-- title:
--   Sz: pow
-- statement:
--   The Sz construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L39-L42

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

theorem GlobalTheory.ConjSize.Sz.pow {z : ℂ} {B : ℝ} (h : Sz ι τ z B) (n : ℕ) : Sz ι τ (z ^ n) (B ^ n) := by sorry
