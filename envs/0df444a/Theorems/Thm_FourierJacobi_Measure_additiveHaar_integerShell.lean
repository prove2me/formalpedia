-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_integerShell
-- name    : FourierJacobi.Measure.additiveHaar_integerShell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:49:09.447187+00:00
-- url     : https://prove2.me/theorems/a726eccf-f311-59a1-bc89-0c59d86da9d8
-- title:
--   Measure: additive Haar integer Shell
-- statement:
--   The same shell-volume formula as an equality in the measure's native
--   extended nonnegative real codomain.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L278-L285
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L278-L285

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.integerShells_additiveHaar_regular

theorem FourierJacobi.Measure.additiveHaar_integerShell (n : ℤ) :
    additiveHaar K (integerShell K n) =
      ENNReal.ofReal ((1 - (residueCardinality K : ℝ)⁻¹) *
        (residueCardinality K : ℝ) ^ (-n)) := by sorry
