-- Prove2me | Theorems.Thm_GlobalTheory_mem_closure_of_forall_dual_vanish
-- name    : GlobalTheory.mem_closure_of_forall_dual_vanish
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:32.201193+00:00
-- url     : https://prove2.me/theorems/88ee3160-16fe-4352-8435-aa3f7ee2eb99
-- title:
--   Global Theory: mem closure of forall dual vanish
-- statement:
--   The Global Theory construction uses the mem closure of forall dual vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemClosureOfForallDualVanish.lean#L7-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemClosureOfForallDualVanish.lean#L7-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemClosureOfForallDualVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex

theorem GlobalTheory.mem_closure_of_forall_dual_vanish :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by sorry
