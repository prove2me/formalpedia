-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_exists_primitive
-- name    : GlobalTheory.BadShare.exists_primitive
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:29:52.800272+00:00
-- url     : https://prove2.me/theorems/915efd78-b010-4c89-8ce2-71310c57db30
-- title:
--   Bad Share: exists primitive
-- statement:
--   The Bad Share construction uses the exists primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L325-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L325-L349

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

theorem GlobalTheory.BadShare.exists_primitive (d : ℕ) (hd : d ≠ 0) : ∃ P : (ZMod g)[X], P.Monic ∧ Irreducible P ∧ P.natDegree = d ∧
    ∀ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∀ n : ℕ, x ^ n = 1 ↔ g ^ d - 1 ∣ n := by sorry
