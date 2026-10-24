-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_derivative_preserves_jets_zero
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:38:00.072132+00:00
-- url     : https://prove2.me/theorems/92fdbf92-9a78-4a80-9b7a-aeab60f907fc
-- title:
--   Zeroth logarithmic frame derivative preserves weighted jets
-- statement:
--   This is the zero-index case of the frame derivative defined in the source as X 0 times pderiv 0 plus the sum of successor partial derivatives. Prove the aggregate formalJet identity: applying formalJet to this frame derivative agrees with multiplying the formalJet derivative in coordinate 0 by 1 + X 0. Its coefficient at exponent a is a linear combination of coefficients of formalJet F at a and a + e₀. If the output weight is below H - v 0, both input weights are strictly below H because v 0 is positive, so hjet makes both coefficients zero. The strict output boundary remains unconstrained, and a negative output threshold is vacuous. A proof route is to verify the substitution derivative identity on polynomial generators and products, using the formal-series derivative of log (1 + X 0), derive the coefficient formula, then apply the two strict weight inequalities. This removes the zero-index case split from the parent; the derivative identity and its coefficient and weight argument remain the core work of this child.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets_zero {m K : Nat} (c : Fin K → Fin m → Complex) (v : Fin (m + 1) → Rat) (H : Real) (h0 : 0 < (v 0 : Real)) (F : MvPolynomial (Fin (m + 1)) Complex) (hjet : logarithmicJetBound c v H F) : logarithmicJetBound c v (H - (v 0 : Real)) (logarithmicFrameDerivative 0 F) := by sorry
