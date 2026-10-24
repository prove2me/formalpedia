-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_derivation_extendRatFunc
-- name    : OAI.PiExponent.FormalInterpolation.derivation_extendRatFunc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:00:32.291007+00:00
-- url     : https://prove2.me/theorems/ba5ee7f0-4d71-49d1-99ed-d88f3cbc8ac1
-- title:
--   Extend a polynomial derivation to rational functions
-- statement:
--   Every K-derivation from K[X] to K(X), with the natural K(X)-module structure on its codomain, extends to a K-derivation from K(X) to itself, preserving its values on polynomials.

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivation

open RatFunc

theorem OAI.PiExponent.FormalInterpolation.derivation_extendRatFunc
    (K : Type) [Field K]
    (D : Derivation K (Polynomial K) (RatFunc K)) :
    ∃ d : Derivation K (RatFunc K) (RatFunc K),
      ∀ p : Polynomial K,
        d (algebraMap (Polynomial K) (RatFunc K) p) = D p := by sorry
