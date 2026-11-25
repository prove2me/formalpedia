-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_closure_of_forall_clm_vanish
-- name    : GlobalTheory.T.mem_closure_of_forall_clm_vanish
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:08.817405+00:00
-- url     : https://prove2.me/theorems/05450dea-485a-51a5-a357-c5799627e186
-- title:
--   T: mem closure of forall clm vanish
-- statement:
--   The T construction uses the mem closure of forall clm vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemClosureOfForallDualVanishStatement.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemClosureOfForallDualVanishStatement.lean#L5-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemClosureOfForallDualVanish
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemClosureOfForallDualVanishStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_closure_of_forall_clm_vanish : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by sorry
