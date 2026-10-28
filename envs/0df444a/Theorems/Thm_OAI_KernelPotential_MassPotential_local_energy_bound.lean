-- Prove2me | Theorems.Thm_OAI_KernelPotential_MassPotential_local_energy_bound
-- name    : OAI.KernelPotential.MassPotential.local_energy_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:02:05.598446+00:00
-- url     : https://prove2.me/theorems/efba541f-e2a7-4343-b9c4-b7bc97e223b2
-- title:
--   OAI.KernelPotential.MassPotential.local_energy_bound: intermediate lemma from OpenAI, Localization costs and information growth for exact Gaussian observations
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KernelPotential.actual_row_drift`, `OAI.KernelPotential.kernel_coercivity` and `OAI.AllScaleInverseVolume.inverse_volume_without_support`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Localization costs and information growth for exact Gaussian observations*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KernelPotential.MassPotential.local_energy_bound` of [lean/OAI/Probability/GaussianInformation/GaussianInformation/Kernel/LocalEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianInformation/GaussianInformation/Kernel/LocalEnergy.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.KernelPotential.MassPotential`, with `open MeasureTheory ProbabilityTheory Metric Set`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory`, `open MeasureTheory`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal`, `open Coercivity Bayes NoisyDrift`):
--
--   ```lean
--   lemma local_energy_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
--       (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (hρ : ρ ≤ sphereProbability d)
--       (rule : LocalRule (d/16) d N) :
--       (∑ w,energy (ρ.withDensity (fun s => ENNReal.ofReal (rule.response w s)))) ≤
--         energy ρ+(ρ univ).toReal*(95*(d:ℝ)+6*Real.log (1/(ρ univ).toReal)/(d:ℝ)+
--           2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.KernelPotential.MassPotential.energy`, `OAI.KernelPotential.NoisyDrift.LocalRule` and `OAI.KernelPotential.NoisyDrift.LocalRule.response` (definitions bundle `OAIQWRLC001` of this split); `OAI.KernelPotential.Ambient` and `OAI.KernelPotential.sphereProbability` (the published bundle `Def_GaussianInformation_003`).
--
--   **Used by.** The proof of `OAI.KernelPotential.actual_row_drift` of this split imports it.
-- source:
--   OpenAI, Localization costs and information growth for exact Gaussian observations, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianInformation/GaussianInformation/Kernel/LocalEnergy.lean (declaration OAI.KernelPotential.MassPotential.local_energy_bound)

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

namespace KernelPotential.MassPotential
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Coercivity Bayes NoisyDrift
lemma local_energy_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 0 < N)
    (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (hρ : ρ ≤ sphereProbability d)
    (rule : LocalRule (d/16) d N) :
    (∑ w,energy (ρ.withDensity (fun s => ENNReal.ofReal (rule.response w s)))) ≤
      energy ρ+(ρ univ).toReal*(95*(d:ℝ)+6*Real.log (1/(ρ univ).toReal)/(d:ℝ)+
        2*Real.log (N:ℝ)/(d:ℝ)+Real.log (N:ℝ)/(d/16:ℕ)) := by
  sorry
end KernelPotential.MassPotential

end OAI
end
