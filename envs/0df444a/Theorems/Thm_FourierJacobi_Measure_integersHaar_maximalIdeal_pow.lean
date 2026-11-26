-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integersHaar_maximalIdeal_pow
-- name    : FourierJacobi.Measure.integersHaar_maximalIdeal_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:11.627544+00:00
-- url     : https://prove2.me/theorems/19616b31-e299-532d-aafb-a97e24edf70f
-- title:
--   Measure: integers Haar maximal Ideal pow
-- statement:
--   Every nonnegative valuation ball has its expected volume, using actual Haar measure.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L109-L116
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L109-L116

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal NNReal
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.localField_t2Space
variable [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Measure.integersHaar_maximalIdeal_pow (n : ℕ) :
    integersHaar K ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by sorry
