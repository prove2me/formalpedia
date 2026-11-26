-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_integerBall
-- name    : FourierJacobi.Measure.additiveHaar_integerBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:14.067025+00:00
-- url     : https://prove2.me/theorems/0062c144-8acf-4d55-93c3-17ceb1521272
-- title:
--   Measure: additive Haar integer Ball
-- statement:
--   All integer balls have the expected finite, positive Haar measure.
--   The proof includes negative integers, using the group-homomorphism law for
--   the genuine Haar scaling character.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L235-L240
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L235-L240

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

theorem FourierJacobi.Measure.additiveHaar_integerBall (n : ℤ) :
    additiveHaar K (integerBall K n) =
      (((residueCardinality K : ℝ≥0)⁻¹) ^ n : ℝ≥0) := by sorry
