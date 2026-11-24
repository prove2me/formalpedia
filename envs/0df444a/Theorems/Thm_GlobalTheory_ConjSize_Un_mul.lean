-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Un_mul
-- name    : GlobalTheory.ConjSize.Un.mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:13.019459+00:00
-- url     : https://prove2.me/theorems/8a0e0ce1-cb54-44cf-8663-e8ac9b0d8943
-- title:
--   Un: mul
-- statement:
--   The Un construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L75-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul

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

theorem GlobalTheory.ConjSize.Un.mul {z z' : ℂ} (h : Un ι τ z) (h' : Un ι τ z') : Un ι τ (z * z') := by sorry
