-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integerBall_isOpen
-- name    : FourierJacobi.Measure.integerBall_isOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:44:17.68284+00:00
-- url     : https://prove2.me/theorems/379a1152-ac7a-5835-9a8d-b7cc68b52128
-- title:
--   Measure: integer Ball is Open
-- statement:
--   The Measure construction uses the integer Ball is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L190-L193
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L190-L193

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

theorem FourierJacobi.Measure.integerBall_isOpen (n : ℤ) : IsOpen (integerBall K n) := by sorry
