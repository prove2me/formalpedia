-- Prove2me | Theorems.Thm_OAI_CurrentProjection_actual_fresh_row_bound
-- name    : OAI.CurrentProjection.actual_fresh_row_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-24T23:55:11.124678+00:00
-- url     : https://prove2.me/theorems/1a5504b2-44bd-436c-bf47-6ec11976dcd6
-- title:
--   OAI.CurrentProjection.actual_fresh_row_bound: intermediate lemma from OpenAI, Replacing Gaussian observations in memory-constrained inference
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CurrentProjection.fiberBlockMain`, `OAI.CurrentProjection.mixedMomentMain`, `OAI.CurrentProjection.hybridBlockMain`, `OAI.CurrentProjection.fiberTwoPointMain`, `OAI.CurrentProjection.actualRowSourceMain`, `OAI.CurrentProjection.actualRowRefinement`, `OAI.CurrentProjection.twoLabelComparisonMain`, `OAI.CurrentProjection.oneLevelComparisonMain` and `OAI.CurrentProjection.actualRowSourceRefinement`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Replacing Gaussian observations in memory-constrained inference*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CurrentProjection.actual_fresh_row_bound` of [lean/OAI/Probability/GaussianReplacement/RowOrder.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianReplacement/RowOrder.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentProjection`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped ENNReal NNReal RealInnerProductSpace Topology`, `open InnerProductSpace`, `open InformationTheory`):
--
--   ```lean
--   lemma actual_fresh_row_bound {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
--       (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
--       (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
--       (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
--       (hfresh : freshSlope P.fst r ≠ ∞) (hnext : freshSlope P.fst (r+1) ≠ ∞)
--       (hlabel : (residualLabelLaw P r).snd = gaussianReal 0 1) :
--       singleReference (liftActualLaw P r) ≠ ∞ ∧
--       (singleReference (liftActualLaw P r)).toReal ≤
--         (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal +
--         (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q + hybridRowConstant +
--         (freshSlope P.fst (r+1)).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentProjection.Observations`, `OAI.CurrentProjection.freshSlope`, `OAI.CurrentProjection.hybridRowConstant`, `OAI.CurrentProjection.liftActualLaw`, `OAI.CurrentProjection.residualLabelLaw` and `OAI.CurrentProjection.singleReference` (definitions bundle `OAIQWCP001` of this split); `OAI.CurrentProjection.Rows`, `OAI.CurrentProjection.Sphere` and `OAI.CurrentProjection.Vector` (the published bundle `Def_GaussianReplacement`).
--
--   **Used by.** The proof of `OAI.CurrentProjection.hybridBlockMain` of this split imports it.
-- source:
--   OpenAI, Replacing Gaussian observations in memory-constrained inference, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianReplacement/RowOrder.lean (declaration OAI.CurrentProjection.actual_fresh_row_bound)

import Mathlib
import Definitions.Def_GaussianReplacement
import Definitions.Def_OAIQWCP001

section

attribute [-instance] _root_.OAI.CurrentProjection.endingRowLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

attribute [fun_prop] measurable_ownObservations

lemma actual_fresh_row_bound {d r q : ℕ} [Nonempty (Sphere d)] {C : Type*} [MeasurableSpace C]
    (P : Measure ((C×Sphere d)×Vector d)) [IsProbabilityMeasure P]
    (hKL : klDiv P (P.fst.prod (stdGaussian (Vector d))) ≠ ∞)
    (hr : r ≤ d) (hd : d ≤ 8*r) (hq : 1 ≤ q) (hqr : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (hfresh : freshSlope P.fst r ≠ ∞) (hnext : freshSlope P.fst (r+1) ≠ ∞)
    (hlabel : (residualLabelLaw P r).snd = gaussianReal 0 1) :
    singleReference (liftActualLaw P r) ≠ ∞ ∧
    (singleReference (liftActualLaw P r)).toReal ≤
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal +
      (klDiv P (P.fst.prod (stdGaussian (Vector d)))).toReal / q + hybridRowConstant +
      (freshSlope P.fst (r+1)).toReal := by
  sorry

end CurrentProjection

end

end OAI
end
