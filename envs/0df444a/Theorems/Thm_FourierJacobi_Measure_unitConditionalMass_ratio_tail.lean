-- Prove2me | Theorems.Thm_FourierJacobi_Measure_unitConditionalMass_ratio_tail
-- name    : FourierJacobi.Measure.unitConditionalMass_ratio_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:48:29.5381+00:00
-- url     : https://prove2.me/theorems/9f00501c-fcc7-45fc-be86-43dad4b14018
-- title:
--   Measure: unit Conditional Mass ratio tail
-- statement:
--   Actual ratio-cancellation tails for a unit numerator and Haar-uniform integral
--   units. The valuation inequality includes the infinite-depth point, with no
--   incorrect finite value assigned to it.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L355-L374
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L355-L374

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

theorem FourierJacobi.Measure.unitConditionalMass_ratio_tail (π : 𝒪[K]) (hπ : 𝓂[K] = Ideal.span {π})
    (a : 𝒪[K]ˣ) (n : ℕ) :
    unitConditionalMass K {x : 𝒪[K] | x ∈ integralUnits K ∧
      valuation K (((a : 𝒪[K]) : K) / (x : K) - 1) ≤
        valuation K (π : K) ^ (n + 1)} =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by sorry
