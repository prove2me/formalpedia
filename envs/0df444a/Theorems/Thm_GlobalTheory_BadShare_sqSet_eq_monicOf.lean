-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_sqSet_eq_monicOf
-- name    : GlobalTheory.BadShare.sqSet_eq_monicOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:52.124816+00:00
-- url     : https://prove2.me/theorems/bf2b9b65-4157-4fe4-8de3-f048021ed20c
-- title:
--   Bad Share: sq Set eq monic Of
-- statement:
--   The Bad Share construction uses the sq Set eq monic Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L218-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L218-L219

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

theorem GlobalTheory.BadShare.sqSet_eq_monicOf (N : ℕ) : sqSet g N =
    (Finset.univ.image fun c : Fin N → ZMod g => Formalism.CyclotomicNorms.monicOf c).filter fun f => Squarefree f ∧ f.coeff 0 ≠ 0 := by sorry
