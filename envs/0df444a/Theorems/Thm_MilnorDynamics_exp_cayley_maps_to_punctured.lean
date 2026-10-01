-- Prove2me | Theorems.Thm_MilnorDynamics_exp_cayley_maps_to_punctured
-- name    : MilnorDynamics.exp_cayley_maps_to_punctured
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:39:06.832874+00:00
-- url     : https://prove2.me/theorems/db1444b1-5d50-4112-984a-b3e3ccdbf1f1
-- title:
--   The exponential of the Cayley transform maps the disc into the twice-punctured plane
-- statement:
--   Let p z = exp((z+1)/(1-z)). The value p z is never 0 because the complex exponential never vanishes, and it is never 1 because exp u = 1 forces u = 2*pi*i*n, which for Re u > 0 forces n = 0 and hence z = -1, a boundary point. Therefore p sends the open unit disc into the complex plane with the two points 0 and 1 removed. This is the MapsTo obligation in Milnor's Lemma 2.5.
-- source:
--   Milnor, Dynamics in One Complex Variable, Lemma 2.5.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open Complex

namespace MilnorDynamics

theorem exp_cayley_maps_to_punctured :
    MapsTo (fun z : ℂ => Complex.exp ((z + 1) / (1 - z)))
      (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) := by sorry

end MilnorDynamics
