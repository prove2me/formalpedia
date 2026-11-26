-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_smul_of_canonicalValuation
-- name    : FourierJacobi.Measure.additiveHaar_smul_of_canonicalValuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:00.976269+00:00
-- url     : https://prove2.me/theorems/86af2584-f5fd-43e3-994c-e0fceed3f231
-- title:
--   Measure: additive Haar smul of canonical Valuation
-- statement:
--   The Measure construction uses the additive Haar smul of canonical Valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/UnitScaling.lean#L58-L62
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/UnitScaling.lean#L58-L62

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

theorem FourierJacobi.Measure.additiveHaar_smul_of_canonicalValuation (u : Kˣ) (n : ℤ)
    (hu : localFieldValuation K (u : K) = (n : WithTop ℤ)) (s : Set K) :
    additiveHaar K (u • s) =
      (↑(((residueCardinality K : ℝ≥0)⁻¹) ^ n) : ℝ≥0∞) * additiveHaar K s := by sorry
