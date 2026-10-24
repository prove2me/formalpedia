-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eulerDerivation_exists
-- name    : OAI.PiExponent.FormalInterpolation.eulerDerivation_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:55:38.051254+00:00
-- url     : https://prove2.me/theorems/a536f4d2-1147-4271-8a1d-98b81dd1a818
-- title:
--   Existence of the rational Euler derivation
-- statement:
--   For a characteristic-zero field, there is a derivation of its rational function field that sends the indeterminate to itself.

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic

open RatFunc

theorem OAI.PiExponent.FormalInterpolation.eulerDerivation_exists
    (K : Type) [Field K] [CharZero K] :
    ∃ d : Derivation K (RatFunc K) (RatFunc K),
      d RatFunc.X = RatFunc.X := by sorry
