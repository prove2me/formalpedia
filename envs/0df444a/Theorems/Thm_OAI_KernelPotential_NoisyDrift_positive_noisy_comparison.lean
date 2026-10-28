-- Prove2me | Theorems.Thm_OAI_KernelPotential_NoisyDrift_positive_noisy_comparison
-- name    : OAI.KernelPotential.NoisyDrift.positive_noisy_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:02:06.63854+00:00
-- url     : https://prove2.me/theorems/b8afc666-4ea2-4109-92c2-fa06f1e44dcc
-- title:
--   OAI.KernelPotential.NoisyDrift.positive_noisy_comparison: intermediate lemma from OpenAI, Localization costs and information growth for exact Gaussian observations
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KernelPotential.actual_row_drift`, `OAI.KernelPotential.kernel_coercivity` and `OAI.AllScaleInverseVolume.inverse_volume_without_support`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Localization costs and information growth for exact Gaussian observations*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KernelPotential.NoisyDrift.positive_noisy_comparison` of [lean/OAI/Probability/GaussianInformation/GaussianInformation/Kernel/ConditionalCharge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianInformation/GaussianInformation/Kernel/ConditionalCharge.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.KernelPotential.NoisyDrift`, with `open MeasureTheory ProbabilityTheory Metric Set`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory`, `open MeasureTheory`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal`, `open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity Sphere`):
--
--   ```lean
--   lemma positive_noisy_comparison {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
--       [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
--       (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (hηL : η ≤ Scale.radius (DriftCutoff.level d H)) :
--       (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w))) ≤
--         Phi ν+10*(d:ℝ)+2*Real.log ((DriftCutoff.level d H:ℝ)+2)+
--           ∫ t : Ambient d × Observation (d/16) d × Fin N,postCharge ν rule η t.2.1 t.2.2
--             ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel
--   ```
--
--   **Definitions.** The statement is written with `OAI.KernelPotential.Bayes.mass`, `OAI.KernelPotential.Bayes.post`, `OAI.KernelPotential.DriftCutoff.level`, `OAI.KernelPotential.Noise.Observation`, `OAI.KernelPotential.Noise.observationBase`, `OAI.KernelPotential.Noise.observationKernel`, `OAI.KernelPotential.NoisyDrift.PositiveRule`, `OAI.KernelPotential.NoisyDrift.postCharge`, `OAI.KernelPotential.Scale.radius`, `OAI.KernelPotential.DriftTools.FiniteReference.joint`, `OAI.KernelPotential.NoisyDrift.PositiveRule.kernel` and `OAI.KernelPotential.NoisyDrift.PositiveRule.response` (definitions bundle `OAIQWRLC001` of this split); `OAI.KernelPotential.Ambient`, `OAI.KernelPotential.Phi` and `OAI.KernelPotential.sphereProbability` (the published bundle `Def_GaussianInformation_003`).
--
--   **Used by.** The proof of `OAI.KernelPotential.MassPotential.local_energy_bound` of this split imports it.
-- source:
--   OpenAI, Localization costs and information growth for exact Gaussian observations, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianInformation/GaussianInformation/Kernel/ConditionalCharge.lean (declaration OAI.KernelPotential.NoisyDrift.positive_noisy_comparison)

import Mathlib
import Definitions.Def_GaussianInformation_003
import Definitions.Def_OAIQWRLC001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity Sphere

lemma positive_noisy_comparison {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (hηL : η ≤ Scale.radius (DriftCutoff.level d H)) :
    (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w))) ≤
      Phi ν+10*(d:ℝ)+2*Real.log ((DriftCutoff.level d H:ℝ)+2)+
        ∫ t : Ambient d × Observation (d/16) d × Fin N,postCharge ν rule η t.2.1 t.2.2
          ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel := by
  sorry
end KernelPotential.NoisyDrift

end OAI
end
