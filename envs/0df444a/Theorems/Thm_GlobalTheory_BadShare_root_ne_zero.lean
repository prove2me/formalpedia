-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_root_ne_zero
-- name    : GlobalTheory.BadShare.root_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:59:37.011929+00:00
-- url     : https://prove2.me/theorems/46eb1eac-0fd4-439b-838e-24be433038a5
-- title:
--   Bad Share: root ne zero
-- statement:
--   The Bad Share construction uses the root ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L171-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L171-L178

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

theorem GlobalTheory.BadShare.root_ne_zero {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) {x : AlgebraicClosure (ZMod g)}
    (hx : x ∈ f.aroots (AlgebraicClosure (ZMod g))) : x ≠ 0 := by sorry
