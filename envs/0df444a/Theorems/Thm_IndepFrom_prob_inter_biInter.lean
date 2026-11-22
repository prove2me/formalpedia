-- Prove2me | Theorems.Thm_IndepFrom_prob_inter_biInter
-- name    : IndepFrom.prob_inter_biInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:48.260658+00:00
-- url     : https://prove2.me/theorems/5320771e-91df-42a5-bf0d-7957b6104d10
-- title:
--   Indep From: prob inter bi Inter
-- statement:
--   The Indep From construction uses the prob inter bi Inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L86-L90
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L86-L90

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

theorem IndepFrom.prob_inter_biInter (h : IndepFrom s t P) {C : Set ι} {A : ι → Set Ω}
    (hC : C.Countable) (ht : ∀ i ∈ C, A i ∈ t ∨ (A i)ᶜ ∈ t) :
    P (s ∩ ⋂ i ∈ C, A i) = P s * P (⋂ i ∈ C, A i) := by sorry
