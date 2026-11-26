-- Prove2me | Theorems.Thm_FourierJacobi_Measure_extendedNegLog_eq_coe_iff
-- name    : FourierJacobi.Measure.extendedNegLog_eq_coe_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:44:18.345894+00:00
-- url     : https://prove2.me/theorems/9142fbff-97ba-4849-908e-c0d6cf22db44
-- title:
--   Measure: extended Neg Log eq coe iff
-- statement:
--   The Measure construction uses the extended Neg Log eq coe iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L23-L34
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/IntegerShells.lean#L23-L34

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

theorem FourierJacobi.Measure.extendedNegLog_eq_coe_iff (z : ℤᵐ⁰) (n : ℤ) :
    extendedNegLog z = (n : WithTop ℤ) ↔ z = WithZero.exp (-n) := by sorry
