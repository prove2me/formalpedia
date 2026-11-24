-- Prove2me | Theorems.Thm_MeasureTheory_cantorMeasure_real_cylinderOn
-- name    : MeasureTheory.cantorMeasure_real_cylinderOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:29:32.570929+00:00
-- url     : https://prove2.me/theorems/1a42736d-b2b5-44a1-9711-dcb619de2349
-- title:
--   Measure Theory: cantor Measure real cylinder On
-- statement:
--   Real-valued form of `cantorMeasure_cylinderOn`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/SecondMoment.lean#L35-L37
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/SecondMoment.lean#L35-L37

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_AddUN_SecondMoment
set_option autoImplicit false
@[expose] public section
public section
open Set MeasureTheory
open MeasureTheory

theorem MeasureTheory.cantorMeasure_real_cylinderOn (B : Finset ℕ) (v : ℕ → Bool) :
    cantorMeasure.real (cylinderOn B v) = (1 / 2) ^ B.card := by sorry
