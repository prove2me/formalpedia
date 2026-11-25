-- Prove2me | Theorems.Thm_Newton_holder_inequality
-- name    : Newton.holder_inequality
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:30:46.84547+00:00
-- url     : https://prove2.me/theorems/24ae548d-0255-4b2a-ba9b-7fbaf8cf898b
-- title:
--   Newton: holder inequality
-- statement:
--   **Hölder's inequality (general form with eLpNorm).**
--
--   For conjugate exponents 1 ≤ p, q ≤ ∞ with 1/p + 1/q = 1:
--     ∫ |f · g| dμ ≤ ‖f‖_{L^p(μ)} · ‖g‖_{L^q(μ)}
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Holder.lean#L147-L549
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Holder.lean#L147-L549

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

theorem Newton.holder_inequality
    (p q : ℝ≥0∞)
    (hpq : IsConjugateExponent p q)
    (f : α → E) (g : α → F)
    (hf : MemLp f p μ)
    (hg : MemLp g q μ) :
    Integrable (fun x => ‖f x‖ * ‖g x‖) μ ∧
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by sorry
