-- Prove2me | Theorems.Thm_MilnorDynamics_exp_cayley_differentiable_disk
-- name    : MilnorDynamics.exp_cayley_differentiable_disk
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:38:56.901634+00:00
-- url     : https://prove2.me/theorems/8bb64d78-351c-4e64-a93c-9ae05a2150d1
-- title:
--   The exponential of the Cayley transform is holomorphic on the open unit disc
-- statement:
--   The function z |-> exp((z+1)/(1-z)) is complex differentiable at every point of the open unit disc. The Cayley transform is a rational function whose only pole is at z = 1, a boundary point, and the complex exponential is entire, so the composite is holomorphic on the open disc. This supplies the DifferentiableOn hypothesis of Milnor's Lemma 2.5.
-- source:
--   Milnor, Dynamics in One Complex Variable, Lemma 2.5; holomorphic on the disc as a composition of a rational function with no interior pole and the entire exponential.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open Complex

namespace MilnorDynamics

theorem exp_cayley_differentiable_disk :
    DifferentiableOn ℂ (fun z : ℂ => Complex.exp ((z + 1) / (1 - z))) (Metric.ball 0 1) := by sorry

end MilnorDynamics
