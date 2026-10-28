-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_perturbation_contact_exists
-- name    : OAI.SphericalPerceptronFreeEnergy.source_perturbation_contact_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:16:46.072197+00:00
-- url     : https://prove2.me/theorems/bd759874-b0b0-445e-99e0-c0d0ed77de3b
-- title:
--   OAI.SphericalPerceptronFreeEnergy.source_perturbation_contact_exists: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.source_perturbation_contact_exists` of [lean/OAI/Probability/Perceptron/Interpolation/PerturbationContact.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Interpolation/PerturbationContact.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma source_perturbation_contact_exists (n k : ℕ) (f : ℝ →ᵇ ℝ)
--       (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
--       (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
--       (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
--       ∃ u ∈ Icc (fun _ : Fin (n+1) => 1) (fun _ => 2),
--         IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
--           sourceExpectedPressure n k f p d h z t v)
--           (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) u
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.quadraticBoxPenalty` and `OAI.SphericalPerceptronFreeEnergy.sourcePenaltyWeight` (definitions bundle `OAIQ61Pf001` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists`, `OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists`, `OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists` and `OAI.SphericalPerceptronFreeEnergy.quantile_pair_reference_exists` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Interpolation/PerturbationContact.lean (declaration OAI.SphericalPerceptronFreeEnergy.source_perturbation_contact_exists)

import Mathlib
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma source_perturbation_contact_exists (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    ∃ u ∈ Icc (fun _ : Fin (n+1) => 1) (fun _ => 2),
      IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
        sourceExpectedPressure n k f p d h z t v)
        (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) u := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
