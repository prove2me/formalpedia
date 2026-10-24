-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_derivative_preserves_jets_succ
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:38:27.600981+00:00
-- url     : https://prove2.me/theorems/cb3dc476-97b1-4a89-9fe6-18f4a9e3e71c
-- title:
--   Successor logarithmic frame derivative preserves weighted jets
-- statement:
--   This is the successor-index case. The formalJet image of the matching successor variable is its constant term plus X i.succ plus a logarithmic series independent of X i.succ, so its matching partial derivative is one. Establish that formalJet commutes with this partial derivative. The output coefficient at exponent a is then a scalar multiple of the input coefficient at a + e_(i.succ). If the output weight is below H - v i.succ, positivity makes the shifted input weight strictly below H, so hjet forces it to vanish. The strict output boundary remains unconstrained, and a negative threshold is vacuous. A proof route is to establish the substitution identity on polynomial generators and products, derive the power-series derivative coefficient formula, and apply the strict weight estimate. This removes the successor case split from the parent; the derivative identity and shifted-weight argument remain the core work of this child.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets_succ {m K : Nat} (c : Fin K → Fin m → Complex) (v : Fin (m + 1) → Rat) (H : Real) (i : Fin m) (hi : 0 < (v i.succ : Real)) (F : MvPolynomial (Fin (m + 1)) Complex) (hjet : logarithmicJetBound c v H F) : logarithmicJetBound c v (H - (v i.succ : Real)) (logarithmicFrameDerivative i.succ F) := by sorry
