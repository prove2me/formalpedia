-- Prove2me | Theorems.Thm_IndepFrom_prob_inter_iInter
-- name    : IndepFrom.prob_inter_iInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:46.713186+00:00
-- url     : https://prove2.me/theorems/cc6a3168-ca5c-4bc0-a27c-d9ade154ffc1
-- title:
--   Indep From: prob inter i Inter
-- statement:
--   The Indep From construction uses the prob inter i Inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L75-L84
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L75-L84

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

theorem IndepFrom.prob_inter_iInter [Countable ι] (h : IndepFrom s t P) {A : ι → Set Ω}
    (ht : ∀ i, A i ∈ t ∨ (A i)ᶜ ∈ t) : P (s ∩ ⋂ i, A i) = P s * P (⋂ i, A i) := by sorry
