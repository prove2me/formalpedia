-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Un_inv
-- name    : GlobalTheory.ConjSize.Un.inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:45.292242+00:00
-- url     : https://prove2.me/theorems/ef70eea1-1bb7-486c-aaaf-4b1faa98b7dd
-- title:
--   Un: inv
-- statement:
--   The Un construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L80-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SplitFlip_IsCoeffRing_inv
import Theorems.Thm_GlobalTheory_SplitFlip_IsRightTranslationIsometric_inv

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

theorem GlobalTheory.ConjSize.Un.inv {z : ℂ} (h : Un ι τ z) : Un ι τ z⁻¹ := by sorry
