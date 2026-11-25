-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_rootsAvoid_iff
-- name    : GlobalTheory.BadShare.rootsAvoid_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:15.751682+00:00
-- url     : https://prove2.me/theorems/dfe0042c-9bdc-400f-977f-7c3dabc9daa7
-- title:
--   Bad Share: roots Avoid iff
-- statement:
--   The Bad Share construction uses the roots Avoid iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L208-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L208-L216

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

theorem GlobalTheory.BadShare.rootsAvoid_iff {c : (ZMod g)ˣ} {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) :
    _root_.GlobalTheory.BadShare.RootsAvoid g c f ↔ ∀ l : ℕ, l.Prime → l ≠ g → ∀ x ∈ f.aroots (AlgebraicClosure (ZMod g)), ∀ a : ℕ,
      x ^ (l ^ a) ≠ (algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g)) ^ (l ^ a) := by sorry
