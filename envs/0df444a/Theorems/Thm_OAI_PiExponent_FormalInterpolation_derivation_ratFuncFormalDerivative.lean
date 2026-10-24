-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_derivation_ratFuncFormalDerivative
-- name    : OAI.PiExponent.FormalInterpolation.derivation_ratFuncFormalDerivative
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:06:32.368726+00:00
-- url     : https://prove2.me/theorems/1dbe7f74-aabd-499b-a77e-3c2b6ca7818b
-- title:
--   Extend polynomial formal differentiation to rational functions
-- statement:
--   The formal derivative on polynomials extends to a K-derivation on the rational function field, agreeing with polynomial differentiation on every polynomial.

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivation

open RatFunc

theorem OAI.PiExponent.FormalInterpolation.derivation_ratFuncFormalDerivative
    (K : Type) [Field K] :
    ∃ δ : Derivation K (RatFunc K) (RatFunc K),
      ∀ p : Polynomial K,
        δ (algebraMap (Polynomial K) (RatFunc K) p) =
          algebraMap (Polynomial K) (RatFunc K) p.derivative := by sorry
