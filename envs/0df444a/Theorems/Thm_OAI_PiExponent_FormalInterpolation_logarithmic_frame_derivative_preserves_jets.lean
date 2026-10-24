-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_derivative_preserves_jets
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T05:57:05.239734+00:00
-- url     : https://prove2.me/theorems/230ad871-0f25-4d5e-8db0-ae52d7fcf646
-- title:
--   A logarithmic frame derivative spends one weighted jet cost
-- statement:
--   For a single frame derivative at coordinate i, vanishing of every formal-jet coefficient of weight strictly below H implies vanishing of every output coefficient of weight strictly below H minus the positive weight of i. For i = 0, the pulled-back operator is `(1 + X 0) ∂₀`, whose coefficient at exponent a uses the input coefficients at a and a + e₀. For i = j.succ, the pulled-back operator is `∂ⱼ₊₁`, whose coefficient uses the input coefficient at a + eⱼ₊₁. In each case the needed input exponents have weight below H. This child removes the frame-word induction and the cost arithmetic from the parent; its remaining core is proving the formalJet/derivative coefficient identities and applying the strict weighted inequalities. The boundary is strict as in the parent definition: coefficients at weight exactly H minus the cost are not asserted to vanish. If the resulting threshold is negative, the conclusion is vacuous.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (H : Real)
    (i : Fin (m + 1)) (hi : 0 < (v i : Real))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hjet : logarithmicJetBound c v H F) :
    logarithmicJetBound c v (H - (v i : Real))
      (logarithmicFrameDerivative i F) := by sorry
