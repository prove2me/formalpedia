-- Prove2me | Theorems.Thm_IndepFrom_cond_biInter
-- name    : IndepFrom.cond_biInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:57.145362+00:00
-- url     : https://prove2.me/theorems/46d6191c-553a-4db7-bd35-1d86aa805607
-- title:
--   Indep From: cond bi Inter
-- statement:
--   The Indep From construction uses the cond bi Inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L106-L111
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L106-L111

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
open MeasurableSpace Measure
variable {s : Set Ω} {t t' : Set (Set Ω)}
variable [IsProbabilityMeasure P]

theorem IndepFrom.cond_biInter (h : IndepFrom s t P) {C : Set ι}
    {A : ι → Set Ω} (hC : C.Countable) (hs : MeasurableSet s) (ht : ∀ i ∈ C, A i ∈ t ∨ (A i)ᶜ ∈ t)
    (ht₀ : P (⋂ i ∈ C, A i) ≠ 0) :
    P[s | ⋂ i ∈ C, A i] = P s := by sorry
