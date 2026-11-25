-- Prove2me | Theorems.Thm_GlobalTheory_IdxInt_cint_eq_of_fine
-- name    : GlobalTheory.IdxInt.cint_eq_of_fine
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:31:16.713737+00:00
-- url     : https://prove2.me/theorems/179231ec-1f83-482f-9cce-a67ced169ed7
-- title:
--   Idx Int: cint eq of fine
-- statement:
--   The Idx Int construction uses the cint eq of fine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralEqOfFineSubgroup.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralEqOfFineSubgroup.lean#L74-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroup
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
open Function

theorem GlobalTheory.IdxInt.cint_eq_of_fine : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ),
    _root_.GlobalTheory.IdxInt.Fine A φ B → _root_.GlobalTheory.IdxInt.cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by sorry
