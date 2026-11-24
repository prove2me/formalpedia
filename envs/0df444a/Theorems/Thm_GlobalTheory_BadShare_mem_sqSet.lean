-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_mem_sqSet
-- name    : GlobalTheory.BadShare.mem_sqSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:02.488805+00:00
-- url     : https://prove2.me/theorems/43e7a4d4-870a-407f-9ae1-db4cf3cbd63a
-- title:
--   Bad Share: mem sq Set
-- statement:
--   The Bad Share construction uses the mem sq Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L225-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L225-L237

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

theorem GlobalTheory.BadShare.mem_sqSet {N : ℕ} {f : (ZMod g)[X]} :
    f ∈ _root_.GlobalTheory.BadShare.sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by sorry
