-- Prove2me | Theorems.Thm_IndepFrom_prob_inter_sInter
-- name    : IndepFrom.prob_inter_sInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:38:57.409112+00:00
-- url     : https://prove2.me/theorems/7b3257b8-e082-4226-afe2-f307f0c53080
-- title:
--   Indep From: prob inter s Inter
-- statement:
--   The Indep From construction uses the prob inter s Inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L92-L95
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LocalLemma.lean#L92-L95

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

theorem IndepFrom.prob_inter_sInter (h : IndepFrom s t P) (ht' : t'.Countable)
    (ht : ∀ i ∈ t', i ∈ t ∨ iᶜ ∈ t) : P (s ∩ ⋂₀ t') = P s * P (⋂₀ t') := by sorry
