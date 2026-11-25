-- Prove2me | Theorems.Thm_Newton_memLp_mul_of_memLp_conjugate
-- name    : Newton.memLp_mul_of_memLp_conjugate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:28:14.652128+00:00
-- url     : https://prove2.me/theorems/6794892f-42bd-4f75-a845-66a6ca9cd51a
-- title:
--   Newton: mem Lp mul of mem Lp conjugate
-- statement:
--   The Newton construction uses the mem Lp mul of mem Lp conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Holder.lean#L553-L569
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Holder.lean#L553-L569

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
open Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Newton.memLp_mul_of_memLp_conjugate
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f : α → ℝ) (g : α → ℝ)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (fun x => f x * g x) μ := by sorry
