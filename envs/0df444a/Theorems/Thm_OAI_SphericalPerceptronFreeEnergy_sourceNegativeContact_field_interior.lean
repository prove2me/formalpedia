-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_sourceNegativeContact_field_interior
-- name    : OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_field_interior
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:14:38.114186+00:00
-- url     : https://prove2.me/theorems/1b080e57-f440-4f37-b73b-854959f74772
-- title:
--   OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_field_interior: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_field_interior` of [lean/OAI/Probability/Perceptron/Variational/BoundaryEstimate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/BoundaryEstimate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma sourceNegativeContact_field_interior {k : ℕ} (w : Fin (k+1)→ℝ)
--       (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1)
--       (P : Measure BrownianPath) [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ)
--       (q r : Fin (k+1)→Time) (hr : Monotone r) (hr1 : (r (Fin.last k):ℝ)<1)
--       {η : ℝ} (hη : 0<η) (hqr : ∀ i, (q i:ℝ)+η≤(r i:ℝ)) (α : ℝ≥0)
--       (H : ℝ) (hH : (entropy (weightedStepTrial w r (fun i => (hw i).le) hw1)).toReal+
--         2*(α:ℝ)*‖f‖ ≤ η*w (Fin.last k)*H) {ε : ℝ} (hε : 0<ε) :
--       ∀ᶠ n : ℕ in atTop, ∀ (p d : Fin (n+1)→ℕ) (δ : ℝ), 0≤δ →
--         ∀ a : SourceContactParameter n k, a∈sourceContactCompactDomain n k α H →
--         sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ a < -ε →
--         a.2.1 (Fin.last k)<H
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.SourceContactParameter` and `OAI.SphericalPerceptronFreeEnergy.weightedStepTrial` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceContactCompactDomain` and `OAI.SphericalPerceptronFreeEnergy.sourceStepContactObjective` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.BrownianPath`, `OAI.SphericalPerceptronFreeEnergy.Time`, `OAI.SphericalPerceptronFreeEnergy.entropy` and `OAI.SphericalPerceptronFreeEnergy.instMeasurableSpaceBrownianPath` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.main` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/BoundaryEstimate.lean (declaration OAI.SphericalPerceptronFreeEnergy.sourceNegativeContact_field_interior)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceNegativeContact_field_interior {k : ℕ} (w : Fin (k+1)→ℝ)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ)
    (q r : Fin (k+1)→Time) (hr : Monotone r) (hr1 : (r (Fin.last k):ℝ)<1)
    {η : ℝ} (hη : 0<η) (hqr : ∀ i, (q i:ℝ)+η≤(r i:ℝ)) (α : ℝ≥0)
    (H : ℝ) (hH : (entropy (weightedStepTrial w r (fun i => (hw i).le) hw1)).toReal+
      2*(α:ℝ)*‖f‖ ≤ η*w (Fin.last k)*H) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (p d : Fin (n+1)→ℕ) (δ : ℝ), 0≤δ →
      ∀ a : SourceContactParameter n k, a∈sourceContactCompactDomain n k α H →
      sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ a < -ε →
      a.2.1 (Fin.last k)<H := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
