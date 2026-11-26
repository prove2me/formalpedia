-- Prove2me | Theorems.Thm_FourierJacobi_Measure_shellConditionalMass_collisionDepth_zero
-- name    : FourierJacobi.Measure.shellConditionalMass_collisionDepth_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:45:10.532555+00:00
-- url     : https://prove2.me/theorems/797a07eb-2b9f-4d89-821b-8061ba73c935
-- title:
--   Measure: shell Conditional Mass collision Depth zero
-- statement:
--   The depth-zero collision mass is (q-2)/(q-1), including all integer shells.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L137-L154
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean#L137-L154

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
variable [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Measure.shellConditionalMass_collisionDepth_zero (a : K) (n : ℤ)
    (ha : localFieldValuation K a = (n : WithTop ℤ)) :
    shellConditionalMass K n (shellCollisionDepth K a n 0) =
      (residueCardinality K - 2) / (residueCardinality K - 1) := by sorry
