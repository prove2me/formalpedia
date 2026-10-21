-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_interpolation_numerics_scaling_stability
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_interpolation_numerics_scaling_stability
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:43:46.135732+00:00
-- url     : https://prove2.me/theorems/d7cd7759-fc73-4b9e-a689-851f02361239
-- title:
--   Strict interpolation numerics survive a small rational column enlargement
-- statement:
--   Any rational weights satisfying the strict logarithmic interpolation numerics admit a rational uniform enlargement of the column weights by a factor strictly above one, while keeping row weights unchanged and preserving the numerics.

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_interpolation_numerics_scaling_stability
    (m K : Nat) (sigma : Rat) (w v : Fin (m + 1) -> Rat)
    (hN : OAI.PiExponent.FormalInterpolation.LogarithmicInterpolationNumerics m K w v sigma) :
    exists t : Real, 1 < t /\
      exists w' v' : Fin (m + 1) -> Rat,
        (forall i, (w' i : Real) = t * (w i : Real)) /\
        (forall i, (v' i : Real) = (v i : Real)) /\
        OAI.PiExponent.FormalInterpolation.LogarithmicInterpolationNumerics
          m K w' v' sigma := by sorry
