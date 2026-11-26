-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_uniformizer_pow
-- name    : FourierJacobi.Measure.additiveHaar_uniformizer_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:44.220826+00:00
-- url     : https://prove2.me/theorems/b462b613-179b-44d5-82c0-2cd953b77f66
-- title:
--   Measure: additive Haar uniformizer pow
-- statement:
--   Nonnegative uniformizer balls in the ambient field have volume q^-n.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L136-L150
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L136-L150

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

theorem FourierJacobi.Measure.additiveHaar_uniformizer_pow (π : 𝒪[K])
    (hπ : 𝓂[K] = Ideal.span {π}) (n : ℕ) :
    additiveHaar K ((fun u : 𝒪[K] => (π : K) ^ n * (u : K)) '' Set.univ) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by sorry
