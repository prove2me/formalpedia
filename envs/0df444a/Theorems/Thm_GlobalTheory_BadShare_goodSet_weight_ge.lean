-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_goodSet_weight_ge
-- name    : GlobalTheory.BadShare.goodSet_weight_ge
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:14.22781+00:00
-- url     : https://prove2.me/theorems/47484609-7157-589f-95a4-9d87653103f3
-- title:
--   Bad Share: good Set weight ge
-- statement:
--   The Bad Share construction uses the good Set weight ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GoodSquarefreeLabelTuplesWeightGe.lean#L91-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GoodSquarefreeLabelTuplesWeightGe.lean#L91-L236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_OneSubTwoDivLeSquarefreeLabelMassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassRootsNotDistinctLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassHasDivisorOfDegreeLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassNoLargePrimeFactorLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GoodSquarefreeLabelTuplesWeightGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g} {ι : Type} [Fintype ι] {N : ℕ}

theorem GlobalTheory.BadShare.goodSet_weight_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ (N m q d : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → 2 ^ 12 ≤ g → (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → 1 - (badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / g) ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by sorry
