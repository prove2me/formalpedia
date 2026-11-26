-- Prove2me | Theorems.Thm_FourierJacobi_Measure_iUnion_integerShell_eq
-- name    : FourierJacobi.Measure.iUnion_integerShell_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:48:58.766243+00:00
-- url     : https://prove2.me/theorems/661442db-e0e9-4d64-88ea-f0fd83515abe
-- title:
--   Measure: i Union integer Shell eq
-- statement:
--   The Measure construction uses the i Union integer Shell eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L149-L152
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L149-L152

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

theorem FourierJacobi.Measure.iUnion_integerShell_eq : (⋃ n : ℤ, integerShell K n) = ({0} : Set K)ᶜ := by sorry
