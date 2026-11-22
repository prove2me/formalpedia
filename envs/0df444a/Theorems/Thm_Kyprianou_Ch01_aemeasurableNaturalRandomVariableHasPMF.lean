-- Prove2me | Theorems.Thm_Kyprianou_Ch01_aemeasurableNaturalRandomVariableHasPMF
-- name    : Kyprianou.Ch01.aemeasurableNaturalRandomVariableHasPMF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:46:48.273964+00:00
-- url     : https://prove2.me/theorems/a0bac52b-4dd3-4b10-b9e8-e668b57e7587
-- title:
--   A probability law of an almost-everywhere measurable natural random variable is a PMF with exact singleton masses
-- statement:
--   For any almost-everywhere measurable ℕ-valued random variable on a probability space, use the pushforward measure and the existing Mathlib `Measure.isProbabilityMeasure_map` plus `Measure.toPMF` to produce a genuine PMF with exactly the event probabilities of the original random variable. The pinned signatures `Measure.toPMF_apply` and `Measure.map_apply_of_aemeasurable` give the singleton equality. This finite concise lemma is needed for the inverse Lamperti conservative-law construction: convert the transformed compound-Poisson state random variable to an actual population transition PMF without inventing a synthetic distribution.
-- source:
--   Kyprianou Ch1 §1.3.4, root ac1b29c6-5525-4344-a03d-7469824736ed, direct parent reverseLampertiNonexplosivePopulationLawExists eedf99b6-d4d0-428c-bd29-d18cc4800986. Pinned Mathlib ProbabilityMassFunction.Basic and Measure.Map.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.aemeasurableNaturalRandomVariableHasPMF
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f : Ω → ℕ) (hf : AEMeasurable f Q) :
    ∃ p : PMF ℕ, ∀ k : ℕ, p k = Q {ω | f ω = k} := by
  sorry
