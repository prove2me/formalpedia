-- Prove2me | Theorems.Thm_GlobalTheory_cancel_summand_nilpotent_or_bijective
-- name    : GlobalTheory.cancel_summand_nilpotent_or_bijective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:42.299107+00:00
-- url     : https://prove2.me/theorems/874392c1-5af5-4af7-bb7c-962ec74abd44
-- title:
--   Global Theory: cancel summand nilpotent or bijective
-- statement:
--   The Global Theory construction uses the cancel summand nilpotent or bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CancelProdSummandNilpotentOrBijective.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CancelProdSummandNilpotentOrBijective.lean#L129-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelProdSummandNilpotentOrBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.cancel_summand_nilpotent_or_bijective : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P],
    (∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f) →
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by sorry
