-- Prove2me | Theorems.Thm_GlobalTheory_linearEquiv_cancel_of_nilpotent_or_bijective
-- name    : GlobalTheory.linearEquiv_cancel_of_nilpotent_or_bijective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:08.549663+00:00
-- url     : https://prove2.me/theorems/c93a449d-5a9c-45ef-92c6-5f6acaf48b63
-- title:
--   Global Theory: linear Equiv cancel of nilpotent or bijective
-- statement:
--   The Global Theory construction uses the linear Equiv cancel of nilpotent or bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CancelProdSummandNilpotentOrBijective.lean#L63-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CancelProdSummandNilpotentOrBijective.lean#L63-L125

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
variable {R M M' P : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup P] [Module R P]

theorem GlobalTheory.linearEquiv_cancel_of_nilpotent_or_bijective
    (hP : ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f)
    (e : (M × P) ≃ₗ[R] (M' × P)) : Nonempty (M ≃ₗ[R] M') := by sorry
