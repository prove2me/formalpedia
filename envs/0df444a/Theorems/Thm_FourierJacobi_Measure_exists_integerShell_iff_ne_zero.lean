-- Prove2me | Theorems.Thm_FourierJacobi_Measure_exists_integerShell_iff_ne_zero
-- name    : FourierJacobi.Measure.exists_integerShell_iff_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:41:52.917883+00:00
-- url     : https://prove2.me/theorems/3e46e110-fcef-4bb2-975d-5083a8c5c939
-- title:
--   Measure: exists integer Shell iff ne zero
-- statement:
--   The Measure construction uses the exists integer Shell iff ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L129-L135
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L129-L135

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

theorem FourierJacobi.Measure.exists_integerShell_iff_ne_zero (x : K) :
    (∃ n : ℤ, x ∈ integerShell K n) ↔ x ≠ 0 := by sorry
