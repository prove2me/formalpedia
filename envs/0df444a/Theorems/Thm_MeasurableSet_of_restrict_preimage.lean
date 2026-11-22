-- Prove2me | Theorems.Thm_MeasurableSet_of_restrict_preimage
-- name    : MeasurableSet.of_restrict_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:34.186748+00:00
-- url     : https://prove2.me/theorems/17e60cee-8641-427b-a9f9-7faf506e935f
-- title:
--   Measurable Set: of restrict preimage
-- statement:
--   The Measurable Set construction uses the of restrict preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L126-L137
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L126-L137

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}

theorem MeasurableSet.of_restrict_preimage {ι β : Type*} [MeasurableSpace β]
    {s : Set ι} {T : Set (s → β)} (hT : (s.restrict ⁻¹' T : Set (ι → β)).Nonempty)
    (h : MeasurableSet (s.restrict ⁻¹' T : Set (ι → β))) :
    MeasurableSet T := by sorry
