-- Prove2me | Theorems.Thm_FourierJacobi_Measure_mem_maximalIdeal_pow_iff_valuation_le
-- name    : FourierJacobi.Measure.mem_maximalIdeal_pow_iff_valuation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:36.688802+00:00
-- url     : https://prove2.me/theorems/7e8d6c4b-800a-48e8-be71-e6920b4b4573
-- title:
--   Measure: mem maximal Ideal pow iff valuation le
-- statement:
--   A chosen generator of the maximal ideal realizes its powers as actual valuation balls.
--   This includes zero, whose multiplicative valuation is zero (additive valuation infinity).
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L127-L133
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L127-L133

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
omit [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Measure.mem_maximalIdeal_pow_iff_valuation_le (π : 𝒪[K])
    (hπ : 𝓂[K] = Ideal.span {π}) (n : ℕ) (x : 𝒪[K]) :
    x ∈ 𝓂[K] ^ n ↔ valuation K (x : K) ≤ valuation K (π : K) ^ n := by sorry
