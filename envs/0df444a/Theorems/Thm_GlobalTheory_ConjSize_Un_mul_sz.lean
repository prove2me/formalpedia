-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Un_mul_sz
-- name    : GlobalTheory.ConjSize.Un.mul_sz
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:27.568667+00:00
-- url     : https://prove2.me/theorems/7ab183cf-603e-46e8-b340-36275bc29d10
-- title:
--   Un: mul sz
-- statement:
--   The Un construction uses the mul sz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L87-L88

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

theorem GlobalTheory.ConjSize.Un.mul_sz {z z' : ℂ} {B : ℝ} (h : Un ι τ z) (h' : Sz ι τ z' B) : Sz ι τ (z * z') B := by sorry
