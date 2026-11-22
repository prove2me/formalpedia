-- Prove2me | Theorems.Thm_IndepFrom_cond_sInter
-- name    : IndepFrom.cond_sInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:39:07.293031+00:00
-- url     : https://prove2.me/theorems/77171594-6c41-409b-9db6-a4d296656999
-- title:
--   Indep From: cond s Inter
-- statement:
--   The Indep From construction uses the cond s Inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L113-L117
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L113-L117

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

theorem IndepFrom.cond_sInter (h : IndepFrom s t P) (hs : MeasurableSet s)
    (ht' : t'.Countable) (ht : ∀ i ∈ t', i ∈ t ∨ iᶜ ∈ t) (ht₀ : P (⋂₀ t') ≠ 0) :
    P[s | ⋂₀ t'] = P s := by sorry
