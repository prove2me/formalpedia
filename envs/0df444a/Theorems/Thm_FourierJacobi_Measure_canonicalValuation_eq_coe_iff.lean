-- Prove2me | Theorems.Thm_FourierJacobi_Measure_canonicalValuation_eq_coe_iff
-- name    : FourierJacobi.Measure.canonicalValuation_eq_coe_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:42:26.590161+00:00
-- url     : https://prove2.me/theorems/1879234a-335d-469b-8a60-7ed37f283466
-- title:
--   Measure: canonical Valuation eq coe iff
-- statement:
--   The Measure construction uses the canonical Valuation eq coe iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L54-L57
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L54-L57

import Definitions.Def_FourierJacobi_Measure_LocalHaar
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_FourierJacobi_Measure_IntegerShells
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open scoped ENNReal NNReal Pointwise WithZero
open FourierJacobi FourierJacobi.Measure
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.integerShells_t2Space

theorem FourierJacobi.Measure.canonicalValuation_eq_coe_iff (x : K) (n : ℤ) :
    localFieldValuation K x = (n : WithTop ℤ) ↔
      discreteValuation K x = WithZero.exp (-n) := by sorry
