-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_Sz_sum
-- name    : GlobalTheory.ConjSize.Sz.sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:43:27.441772+00:00
-- url     : https://prove2.me/theorems/1446b786-6524-416d-9be6-b84851fa9593
-- title:
--   Sz: sum
-- statement:
--   The Sz construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L44-L51

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

theorem GlobalTheory.ConjSize.Sz.sum {α : Type*} (s : Finset α) {f : α → ℂ} {B : α → ℝ} (h : ∀ i ∈ s, Sz ι τ (f i) (B i)) :
    Sz ι τ (∑ i ∈ s, f i) (∑ i ∈ s, B i) := by sorry
