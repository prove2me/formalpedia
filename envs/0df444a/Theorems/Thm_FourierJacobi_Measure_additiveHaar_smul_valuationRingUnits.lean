-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_smul_valuationRingUnits
-- name    : FourierJacobi.Measure.additiveHaar_smul_valuationRingUnits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:00.370269+00:00
-- url     : https://prove2.me/theorems/7b372bfc-c644-5976-a994-e7014563f9b9
-- title:
--   Measure: additive Haar smul valuation Ring Units
-- statement:
--   The Measure construction uses the additive Haar smul valuation Ring Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/UnitScaling.lean#L64-L68
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/UnitScaling.lean#L64-L68

import Definitions.Def_FourierJacobi_Measure_MultiplicativeHaar
import Definitions.Def_FourierJacobi_Measure_UnitScaling
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.unitScaling_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.unitScaling_additiveHaar_regular

theorem FourierJacobi.Measure.additiveHaar_smul_valuationRingUnits (u : Kˣ)
    (hu : u ∈ valuationRingUnits K) (s : Set K) :
    additiveHaar K (u • s) = additiveHaar K s := by sorry
