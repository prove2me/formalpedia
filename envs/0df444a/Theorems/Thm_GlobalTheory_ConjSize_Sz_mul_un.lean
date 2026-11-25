-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Sz_mul_un
-- name    : GlobalTheory.ConjSize.Sz.mul_un
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:52.742506+00:00
-- url     : https://prove2.me/theorems/7da976ec-5fc5-4a62-bc8c-fb79b936715c
-- title:
--   Sz: mul un
-- statement:
--   The Sz construction uses the mul un property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L84-L85

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

theorem GlobalTheory.ConjSize.Sz.mul_un {z z' : ℂ} {B : ℝ} (h : Sz ι τ z B) (h' : Un ι τ z') : Sz ι τ (z * z') B := by sorry
