-- Prove2me | Theorems.Thm_FourierJacobi_Measure_coe_le_iff_neg_add_nonnegative
-- name    : FourierJacobi.Measure.coe_le_iff_neg_add_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:44:34.033402+00:00
-- url     : https://prove2.me/theorems/863602db-f651-48f8-b5f4-5cbdaecbf4ee
-- title:
--   Measure: coe le iff neg add nonnegative
-- statement:
--   The Measure construction uses the coe le iff neg add nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L168-L177
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L168-L177

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

theorem FourierJacobi.Measure.coe_le_iff_neg_add_nonnegative (n : ℤ) (v : WithTop ℤ) :
    (n : WithTop ℤ) ≤ v ↔ 0 ≤ ((-n : ℤ) : WithTop ℤ) + v := by sorry
