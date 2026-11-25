-- Prove2me | Theorems.Thm_GlobalTheory_ExpPow_pow_exp_I_or_inv_injective
-- name    : GlobalTheory.ExpPow.pow_exp_I_or_inv_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:48.241086+00:00
-- url     : https://prove2.me/theorems/be4c76d7-43f3-5352-bf44-15f328bf2652
-- title:
--   Exp Pow: pow exp I or inv injective
-- statement:
--   The Exp Pow construction uses the pow exp I or inv injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PowExpIOrInvInjective.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PowExpIOrInvInjective.lean#L31-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PowExpIOrInvInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExpPow

theorem GlobalTheory.ExpPow.pow_exp_I_or_inv_injective :
    ∀ (a b : ℕ) (w : ℂ), (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) →
      w ^ a = w ^ b → a = b := by sorry
