-- Prove2me | Theorems.Thm_MeasureTheory_integral_mul_aux
-- name    : MeasureTheory.integral_mul_aux
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:29:38.196004+00:00
-- url     : https://prove2.me/theorems/eacc44a8-19e2-4abd-ac43-1f916bba8fae
-- title:
--   Measure Theory: integral mul aux
-- statement:
--   The integral of a product of two functions of the form `ρ 1_E - 1_{E ∩ R}`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/SecondMoment.lean#L51-L76
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/SecondMoment.lean#L51-L76

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_AddUN_SecondMoment
set_option autoImplicit false
@[expose] public section
public section
open Set MeasureTheory
open MeasureTheory

theorem MeasureTheory.integral_mul_aux {E E' R R' : Set (ℕ → Bool)} (hE : MeasurableSet E)
    (hE' : MeasurableSet E') (hR : MeasurableSet R) (hR' : MeasurableSet R') (ρ : ℝ) :
    Integrable (fun w ↦ (ρ * ind E w - ind (E ∩ R) w) * (ρ * ind E' w - ind (E' ∩ R') w))
        cantorMeasure ∧
      ∫ w, (ρ * ind E w - ind (E ∩ R) w) * (ρ * ind E' w - ind (E' ∩ R') w) ∂cantorMeasure =
        ρ ^ 2 * cantorMeasure.real (E ∩ E') - ρ * cantorMeasure.real (E ∩ E' ∩ R') -
          ρ * cantorMeasure.real (E ∩ E' ∩ R) + cantorMeasure.real (E ∩ E' ∩ R ∩ R') := by sorry
