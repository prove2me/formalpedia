-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Sz_nonneg
-- name    : GlobalTheory.ConjSize.Sz.nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:42.152149+00:00
-- url     : https://prove2.me/theorems/5f01a71c-8d63-4225-9b2c-7e27d61b972d
-- title:
--   Sz: nonneg
-- statement:
--   The Sz construction uses the nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L19-L19

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

theorem GlobalTheory.ConjSize.Sz.nonneg {z : ℂ} {B : ℝ} (h : Sz ι τ z B) : 0 ≤ B := by sorry
