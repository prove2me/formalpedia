-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_eulerDerivation_nonzero_constant_obstruction
-- name    : OAI.PiExponent.FormalInterpolation.eulerDerivation_nonzero_constant_obstruction
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:56:18.007651+00:00
-- url     : https://prove2.me/theorems/b0a4ca85-5ddd-44ac-878e-64bd8fdec5ff
-- title:
--   The Euler derivation avoids nonzero constants
-- statement:
--   Any derivation over the base field that sends the rational function indeterminate to itself cannot send a rational function to a nonzero base-field constant.

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic

open RatFunc

theorem OAI.PiExponent.FormalInterpolation.eulerDerivation_nonzero_constant_obstruction
    (K : Type) [Field K] [CharZero K]
    (d : Derivation K (RatFunc K) (RatFunc K))
    (hdX : d RatFunc.X = RatFunc.X) :
    ∀ (r : RatFunc K) (c : K), c ≠ 0 →
      d r ≠ algebraMap K (RatFunc K) c := by sorry
