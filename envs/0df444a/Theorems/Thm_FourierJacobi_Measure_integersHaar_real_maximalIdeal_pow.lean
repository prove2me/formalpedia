-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integersHaar_real_maximalIdeal_pow
-- name    : FourierJacobi.Measure.integersHaar_real_maximalIdeal_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:32.671059+00:00
-- url     : https://prove2.me/theorems/018e8a23-4a21-4193-bb62-256d3ae4bdda
-- title:
--   Measure: integers Haar real maximal Ideal pow
-- statement:
--   The Measure construction uses the integers Haar real maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L215-L218
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L215-L218

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

theorem FourierJacobi.Measure.integersHaar_real_maximalIdeal_pow (n : ℕ) :
    (integersHaar K).real ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) =
      (residueCardinality K : ℝ)⁻¹ ^ n := by sorry
