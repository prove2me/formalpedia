-- Prove2me | Theorems.Thm_FourierJacobi_Measure_intValue_lt_one_iff_le_exp_neg_one
-- name    : FourierJacobi.Measure.intValue_lt_one_iff_le_exp_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:44:00.867963+00:00
-- url     : https://prove2.me/theorems/b91202ce-565a-5626-8c76-95659d5287de
-- title:
--   Measure: int Value lt one iff le exp neg one
-- statement:
--   The Measure construction uses the int Value lt one iff le exp neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L36-L44
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L36-L44

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

theorem FourierJacobi.Measure.intValue_lt_one_iff_le_exp_neg_one (z : ℤᵐ⁰) :
    z < 1 ↔ z ≤ WithZero.exp (-1 : ℤ) := by sorry
