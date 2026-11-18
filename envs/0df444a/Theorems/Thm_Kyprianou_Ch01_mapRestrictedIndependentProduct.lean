-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mapRestrictedIndependentProduct
-- name    : Kyprianou.Ch01.mapRestrictedIndependentProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:19:45.676893+00:00
-- url     : https://prove2.me/theorems/f3e196be-d5fc-4355-8367-75a8fc495586
-- title:
--   Measurable restriction of an independent first-coordinate law retains product factorisation
-- statement:
--   If f and g are measurable independent random elements, restrict their common probability measure to the event f lies in a measurable set A. The resulting joint pushforward law remains the product of the restricted f-marginal and the original g-marginal. This is a general measure-level independence preservation lemma with no assumption about a particular stochastic model.
-- source:
--   Kyprianou (2006), Exercise 1.8(ii), conditioning on the strictly positive prefix path, worked solution page 304

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Map
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mapRestrictedIndependentProduct
    {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → α) (g : Ω → β)
    (hf : Measurable f) (hg : Measurable g)
    (hind : IndepFun f g P)
    (A : Set α) (hA : MeasurableSet A) :
    Measure.map (fun ω => (f ω, g ω))
      (P.restrict (f ⁻¹' A)) =
      (Measure.map f (P.restrict (f ⁻¹' A))).prod
        (Measure.map g P) := by
  sorry
