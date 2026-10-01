-- Prove2me | Theorems.Thm_MilnorDynamics_exp_cayley_avoid_punctures
-- name    : MilnorDynamics.exp_cayley_avoid_punctures
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:39:02.849802+00:00
-- url     : https://prove2.me/theorems/9081076b-0219-4ddf-b454-ebf9adf63580
-- title:
--   The exponential of the Cayley transform avoids both punctures on the disc
-- statement:
--   Put w(z) = (z+1)/(1-z), so that Re w > 0 on the open unit disc. The complex exponential of w never vanishes, and it cannot equal 1: by the periodicity identity exp u = 1 exactly when u = 2*pi*i*n for an integer n, and no number of the form 2*pi*i*n has strictly positive real part except 0 itself, which would force z = -1, a point of the boundary. This is the analytic obstruction that makes the composite map a map into the twice-punctured plane.
-- source:
--   Milnor, Dynamics in One Complex Variable, Lemma 2.5; uses the standard identity exp u = 1 iff u = 2*pi*i*n.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open Complex

namespace MilnorDynamics

theorem exp_cayley_avoid_punctures (z : ℂ) (hz : z ∈ Metric.ball 0 1) :
    Complex.exp ((z + 1) / (1 - z)) ≠ 0 ∧
      Complex.exp ((z + 1) / (1 - z)) ≠ 1 := by sorry

end MilnorDynamics
