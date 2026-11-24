-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_samePart_iff_of_ne_zero
-- name    : GlobalTheory.BadShare.samePart_iff_of_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:59:44.194409+00:00
-- url     : https://prove2.me/theorems/c4ef7f80-cf73-4fd4-aa85-824f3d46ee3b
-- title:
--   Bad Share: same Part iff of ne zero
-- statement:
--   The Bad Share construction uses the same Part iff of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L199-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L199-L202

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

theorem GlobalTheory.BadShare.samePart_iff_of_ne_zero {l : ℕ} (hl : l.Prime) {x y : AlgebraicClosure (ZMod g)} (hx : x ≠ 0)
    (hy : y ≠ 0) : _root_.GlobalTheory.BadShare.SamePart l x y ↔ ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a) := by sorry
