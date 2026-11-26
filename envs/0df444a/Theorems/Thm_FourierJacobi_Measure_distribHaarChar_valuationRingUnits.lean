-- Prove2me | Theorems.Thm_FourierJacobi_Measure_distribHaarChar_valuationRingUnits
-- name    : FourierJacobi.Measure.distribHaarChar_valuationRingUnits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:40.363801+00:00
-- url     : https://prove2.me/theorems/a70c06df-dd41-49fb-91d7-3613e344892f
-- title:
--   Measure: distrib Haar Char valuation Ring Units
-- statement:
--   The Measure construction uses the distrib Haar Char valuation Ring Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/UnitScaling.lean#L39-L43
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/UnitScaling.lean#L39-L43

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

theorem FourierJacobi.Measure.distribHaarChar_valuationRingUnits (u : Kˣ) (hu : u ∈ valuationRingUnits K) :
    distribHaarChar K u = 1 := by sorry
