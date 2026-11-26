-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_maximalIdeal_pow
-- name    : FourierJacobi.Measure.additiveHaar_maximalIdeal_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:36.018934+00:00
-- url     : https://prove2.me/theorems/9de7a227-a904-4f88-9bfd-3ac650a21147
-- title:
--   Measure: additive Haar maximal Ideal pow
-- statement:
--   Ambient local-field volume of the image of the nth maximal-ideal power.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L119-L122
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L119-L122

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

theorem FourierJacobi.Measure.additiveHaar_maximalIdeal_pow (n : ℕ) :
    additiveHaar K ((fun x : 𝒪[K] => (x : K)) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by sorry
