-- Prove2me | Theorems.Thm_MeasureTheory_cantorMeasure_inter_cylinder
-- name    : MeasureTheory.cantorMeasure_inter_cylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:06.991815+00:00
-- url     : https://prove2.me/theorems/e3166db4-f430-49e0-a17b-3b17f9768f8c
-- title:
--   Measure Theory: cantor Measure inter cylinder
-- statement:
--   **Independence.** An event that does not depend on the coordinates in the finite set `B` is
--   independent of every cylinder on `B`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L173-L185
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean#L173-L185

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory

theorem MeasureTheory.cantorMeasure_inter_cylinder {E : Set (ℕ → Bool)} (B : Finset ℕ) (v : ℕ → Bool)
    (hE : Determined (↑B)ᶜ E) :
    cantorMeasure (E ∩ cylinderOn B v) = cantorMeasure E * 2⁻¹ ^ B.card := by sorry
