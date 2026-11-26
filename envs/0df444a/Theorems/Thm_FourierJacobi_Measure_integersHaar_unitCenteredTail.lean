-- Prove2me | Theorems.Thm_FourierJacobi_Measure_integersHaar_unitCenteredTail
-- name    : FourierJacobi.Measure.integersHaar_unitCenteredTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:52.00697+00:00
-- url     : https://prove2.me/theorems/d6fc356c-b33d-4587-b6c0-e94c50220551
-- title:
--   Measure: integers Haar unit Centered Tail
-- statement:
--   The Measure construction uses the integers Haar unit Centered Tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L318-L321
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/LocalHaar.lean#L318-L321

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_FourierJacobi_Measure_NullSets
import Definitions.Def_FourierJacobi_Measure_LocalHaar
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open scoped ENNReal NNReal
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.localField_t2Space
variable [MeasurableSpace K] [BorelSpace K]

theorem FourierJacobi.Measure.integersHaar_unitCenteredTail (a : 𝒪[K]ˣ) (n : ℕ) :
    integersHaar K (unitCenteredTail K a n) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by sorry
