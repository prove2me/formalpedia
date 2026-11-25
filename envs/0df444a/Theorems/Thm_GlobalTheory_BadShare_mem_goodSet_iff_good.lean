-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_mem_goodSet_iff_good
-- name    : GlobalTheory.BadShare.mem_goodSet_iff_good
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:37.344045+00:00
-- url     : https://prove2.me/theorems/b5cade83-a03d-5375-afc4-5f64e08cd7c9
-- title:
--   Bad Share: mem good Set iff good
-- statement:
--   The Bad Share construction uses the mem good Set iff good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L277-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L277-L280

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

theorem GlobalTheory.BadShare.mem_goodSet_iff_good {ι : Type} [Fintype ι] {m N : ℕ} {ch : ι → Fin m → (ZMod g)ˣ}
    {F : ι → (ZMod g)[X]} : F ∈ _root_.GlobalTheory.BadShare.goodSet g N ch ↔ _root_.GlobalTheory.BadShare.Good g N ch F := by sorry
