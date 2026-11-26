-- Prove2me | Theorems.Thm_FourierJacobi_Measure_localField_finite_valuations_ae
-- name    : FourierJacobi.Measure.localField_finite_valuations_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:39:58.95295+00:00
-- url     : https://prove2.me/theorems/84b65e24-6696-5c13-8d40-3d9130f9ae7b
-- title:
--   Measure: local Field finite valuations ae
-- statement:
--   Integer coordinates become legitimate only after null-set removal. The
--   valuation here is constructed from the field's actual valuative relation.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L167-L179
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/NullSets.lean#L167-L179

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]

theorem FourierJacobi.Measure.localField_finite_valuations_ae (z : K) :
    ∀ᵐ p : K × K ∂μ.prod μ, ∃ j h c : ℤ,
      Valuations.localFieldValuation K p.1 = (j : WithTop ℤ) ∧
      Valuations.localFieldValuation K p.2 = (h : WithTop ℤ) ∧
      Valuations.localFieldValuation K (p.2 ^ 2 - p.1 * z) = (c : WithTop ℤ) := by sorry
