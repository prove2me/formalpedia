-- Prove2me | Theorems.Thm_FourierJacobi_Measure_canonicalValuation_measurable
-- name    : FourierJacobi.Measure.canonicalValuation_measurable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:44:23.226124+00:00
-- url     : https://prove2.me/theorems/badd2a56-b100-59a2-ae38-2568a2b4bab3
-- title:
--   Measure: canonical Valuation measurable
-- statement:
--   The canonical extended integer valuation is measurable, including its
--   infinite value at zero. No arbitrary finite value is assigned at zero.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L289-L302
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L289-L302

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

theorem FourierJacobi.Measure.canonicalValuation_measurable [MeasurableSpace (WithTop ℤ)] :
    Measurable (localFieldValuation K) := by sorry
