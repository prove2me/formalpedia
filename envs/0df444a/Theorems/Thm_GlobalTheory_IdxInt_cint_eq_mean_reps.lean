-- Prove2me | Theorems.Thm_GlobalTheory_IdxInt_cint_eq_mean_reps
-- name    : GlobalTheory.IdxInt.cint_eq_mean_reps
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:34:47.685947+00:00
-- url     : https://prove2.me/theorems/63461a4c-cfee-46ac-aa7f-9229cd9e9a60
-- title:
--   Idx Int: cint eq mean reps
-- statement:
--   The Idx Int construction uses the cint eq mean reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralEqMeanOverRepresentatives.lean#L42-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralEqMeanOverRepresentatives.lean#L42-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt
open scoped Pointwise Classical
variable {W : Type} [AddCommGroup W]

theorem GlobalTheory.IdxInt.cint_eq_mean_reps {W : Type} [AddCommGroup W]
    (A B : AddSubgroup W) (φ : W → ℂ) (R : Finset W)
    (hBA : B ≤ A) (hinv : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) (hsupp : ∀ w, w ∉ A → φ w = 0)
    (hRA : ∀ w ∈ R, w ∈ A) (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) :
    _root_.GlobalTheory.IdxInt.Fine A φ B ∧ (R.card : ℕ) = B.relIndex A ∧
      _root_.GlobalTheory.IdxInt.cint A φ = (∑ w ∈ R, φ w) / (R.card : ℂ) := by sorry
