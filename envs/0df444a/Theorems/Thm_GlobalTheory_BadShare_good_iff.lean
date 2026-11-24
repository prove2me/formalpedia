-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_good_iff
-- name    : GlobalTheory.BadShare.good_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:18.387306+00:00
-- url     : https://prove2.me/theorems/ac2b833c-3e12-4faa-8ce5-47ee0106151d
-- title:
--   Bad Share: good iff
-- statement:
--   The Bad Share construction uses the good iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L243-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L243-L271

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {g}

theorem GlobalTheory.BadShare.good_iff {ι : Type} {m N : ℕ} {ch : ι → Fin m → (ZMod g)ˣ} {F : ι → (ZMod g)[X]} :
    _root_.GlobalTheory.BadShare.Good g N ch F ↔ (∀ v, F v ∈ _root_.GlobalTheory.BadShare.sqSet g N) ∧
      (∀ v, _root_.GlobalTheory.BadShare.RootsApart g N (F v)) ∧
      (∀ v j, _root_.GlobalTheory.BadShare.RootsAvoid g (ch v j) (F v) ∧ _root_.GlobalTheory.BadShare.RootsAvoid g (ch v j)⁻¹ (F v)) ∧
      (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ N ∧ ∀ v, _root_.GlobalTheory.BadShare.HasDiv g a (F v)) ∧
      ∃ v, _root_.GlobalTheory.BadShare.HasPrimeFactor g N (F v) := by sorry
