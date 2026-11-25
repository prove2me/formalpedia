-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Un_of_pow_eq_one
-- name    : GlobalTheory.ConjSize.Un.of_pow_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:31.76765+00:00
-- url     : https://prove2.me/theorems/f203f1d0-d8fd-50b0-aff9-bbc953e15d6b
-- title:
--   Un: of pow eq one
-- statement:
--   The Un construction uses the of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L90-L94

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

theorem GlobalTheory.ConjSize.Un.of_pow_eq_one {z : ℂ} (hz : z ∈ Set.range ι) {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) : Un ι τ z := by sorry
