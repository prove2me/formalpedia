-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integerBall_eq_uniformizer_smul
-- name    : FourierJacobi.Measure.integerBall_eq_uniformizer_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:03.135706+00:00
-- url     : https://prove2.me/theorems/7867597f-eb50-409a-8289-c1237b51855a
-- title:
--   Measure: integer Ball eq uniformizer smul
-- statement:
--   The Measure construction uses the integer Ball eq uniformizer smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L179-L188
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L179-L188

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

theorem FourierJacobi.Measure.integerBall_eq_uniformizer_smul (π : 𝒪[K])
    (hπ : localFieldValuation K (π : K) = 1) (n : ℤ) :
    integerBall K n = (canonicalUniformizerUnit K π hπ ^ n) • (𝒪[K] : Set K) := by sorry
