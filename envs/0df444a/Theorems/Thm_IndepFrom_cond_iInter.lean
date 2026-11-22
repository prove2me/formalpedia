-- Prove2me | Theorems.Thm_IndepFrom_cond_iInter
-- name    : IndepFrom.cond_iInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:53.446173+00:00
-- url     : https://prove2.me/theorems/e37e7dea-531b-4d77-8e5d-017ad8167b03
-- title:
--   Indep From: cond i Inter
-- statement:
--   The Indep From construction uses the cond i Inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L99-L104
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L99-L104

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

theorem IndepFrom.cond_iInter [Countable ι] (h : IndepFrom s t P)
    {A : ι → Set Ω} (hs : MeasurableSet s) (ht : ∀ i, A i ∈ t ∨ (A i)ᶜ ∈ t)
    (ht₀ : P (⋂ i, A i) ≠ 0) :
    P[s | ⋂ i, A i] = P s := by sorry
