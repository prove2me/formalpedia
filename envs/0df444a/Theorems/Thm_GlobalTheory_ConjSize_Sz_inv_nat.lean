-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Sz_inv_nat
-- name    : GlobalTheory.ConjSize.Sz.inv_nat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:44.674541+00:00
-- url     : https://prove2.me/theorems/583a14fe-6568-4724-99e3-02aba8328e97
-- title:
--   Sz: inv nat
-- statement:
--   The Sz construction uses the inv nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L68-L69

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

theorem GlobalTheory.ConjSize.Sz.inv_nat (n : ℕ) : Sz ι τ ((n : ℂ)⁻¹) ((n : ℝ)⁻¹) := by sorry
