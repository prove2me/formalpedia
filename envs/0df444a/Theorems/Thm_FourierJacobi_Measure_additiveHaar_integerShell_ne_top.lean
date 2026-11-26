-- Prove2me | Theorems.Thm_FourierJacobi_Measure_additiveHaar_integerShell_ne_top
-- name    : FourierJacobi.Measure.additiveHaar_integerShell_ne_top
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:41:47.519801+00:00
-- url     : https://prove2.me/theorems/6acd112c-d516-49d6-8189-a29147ebb98c
-- title:
--   Measure: additive Haar integer Shell ne top
-- statement:
--   The Measure construction uses the additive Haar integer Shell ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L271-L274
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L271-L274

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
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.integerShells_additiveHaar_regular

theorem FourierJacobi.Measure.additiveHaar_integerShell_ne_top (n : ℤ) :
    additiveHaar K (integerShell K n) ≠ ⊤ := by sorry
