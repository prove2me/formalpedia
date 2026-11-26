-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerBall
-- name    : FourierJacobi.Measure.additiveHaar_real_integerBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:59.746991+00:00
-- url     : https://prove2.me/theorems/d8f0bf73-f281-424e-9af5-02be34d40fc8
-- title:
--   Measure: additive Haar real integer Ball
-- statement:
--   The Measure construction uses the additive Haar real integer Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L247-L249
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L247-L249

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

theorem FourierJacobi.Measure.additiveHaar_real_integerBall (n : ℤ) :
    (additiveHaar K).real (integerBall K n) = (residueCardinality K : ℝ) ^ (-n) := by sorry
