-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_global_contact_density
-- name    : OAI.SphericalPerceptronFreeEnergy.source_global_contact_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:15:28.431868+00:00
-- url     : https://prove2.me/theorems/ff729758-8a6b-463e-a5e0-f57269360d32
-- title:
--   OAI.SphericalPerceptronFreeEnergy.source_global_contact_density: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.source_global_contact_density` of [lean/OAI/Probability/Perceptron/Variational/ContactDensity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/ContactDensity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma source_global_contact_density (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
--       (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
--       (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ)
--       {a : SourceContactParameter n k} (ha : a∈sourceContactCompactDomain n k α H)
--       (hmin : IsMinOn (sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ)
--         (sourceContactCompactDomain n k α H) a) (ht : 0<a.1) :
--       controlValue P f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ ≤
--         sourceDensityIncrement n k f p d a.2.1 (stepCumulative w) a.2.2 a.1
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.SourceContactParameter`, `OAI.SphericalPerceptronFreeEnergy.stepCumulative` and `OAI.SphericalPerceptronFreeEnergy.weightedStepTrial` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceContactCompactDomain`, `OAI.SphericalPerceptronFreeEnergy.sourceDensityIncrement` and `OAI.SphericalPerceptronFreeEnergy.sourceStepContactObjective` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.BrownianPath`, `OAI.SphericalPerceptronFreeEnergy.Time`, `OAI.SphericalPerceptronFreeEnergy.controlValue` and `OAI.SphericalPerceptronFreeEnergy.instMeasurableSpaceBrownianPath` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.main` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/ContactDensity.lean (declaration OAI.SphericalPerceptronFreeEnergy.source_global_contact_density)

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

lemma source_global_contact_density (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ)
    {a : SourceContactParameter n k} (ha : a∈sourceContactCompactDomain n k α H)
    (hmin : IsMinOn (sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ)
      (sourceContactCompactDomain n k α H) a) (ht : 0<a.1) :
    controlValue P f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ ≤
      sourceDensityIncrement n k f p d a.2.1 (stepCumulative w) a.2.2 a.1 := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
