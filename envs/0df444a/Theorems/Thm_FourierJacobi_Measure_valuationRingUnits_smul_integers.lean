-- Prove2me | Theorems.Thm_FourierJacobi_Measure_valuationRingUnits_smul_integers
-- name    : FourierJacobi.Measure.valuationRingUnits_smul_integers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:37.462575+00:00
-- url     : https://prove2.me/theorems/a6eb8885-6bea-450f-9a6f-f61a39466d22
-- title:
--   Measure: valuation Ring Units smul integers
-- statement:
--   The Measure construction uses the valuation Ring Units smul integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/UnitScaling.lean#L21-L31
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/UnitScaling.lean#L21-L31

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
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Measure.valuationRingUnits_smul_integers (u : Kˣ) (hu : u ∈ valuationRingUnits K) :
    u • (𝒪[K] : Set K) = (𝒪[K] : Set K) := by sorry
