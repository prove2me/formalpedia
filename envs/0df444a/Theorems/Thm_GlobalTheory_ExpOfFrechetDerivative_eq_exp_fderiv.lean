-- Prove2me | Theorems.Thm_GlobalTheory_ExpOfFrechetDerivative_eq_exp_fderiv
-- name    : GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:13.29311+00:00
-- url     : https://prove2.me/theorems/cb48fc3f-2357-4a5d-a58e-f8fadd6f291a
-- title:
--   Exp Of Frechet Derivative: eq exp fderiv
-- statement:
--   The Exp Of Frechet Derivative construction uses the eq exp fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqExpFderiv.lean#L7-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqExpFderiv.lean#L7-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqExpFderiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.ExpOfFrechetDerivative

theorem GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    (hd : DifferentiableAt ℂ f (0 : E)) (h0 : f (0 : E) ≠ (0 : ℂ))
    (hmul : ∀ x y : E, f (x + y) = f x * f y) (z : E) :
    f z = Complex.exp ((fderiv ℂ f (0 : E) : E → ℂ) z) := by sorry
