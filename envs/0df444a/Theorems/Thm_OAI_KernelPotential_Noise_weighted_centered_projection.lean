-- Prove2me | Theorems.Thm_OAI_KernelPotential_Noise_weighted_centered_projection
-- name    : OAI.KernelPotential.Noise.weighted_centered_projection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:02:01.195993+00:00
-- url     : https://prove2.me/theorems/c6f6fb84-5a9e-4dc1-b385-5200fb186f42
-- title:
--   OAI.KernelPotential.Noise.weighted_centered_projection: intermediate lemma from OpenAI, Localization costs and information growth for exact Gaussian observations
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KernelPotential.actual_row_drift`, `OAI.KernelPotential.kernel_coercivity` and `OAI.AllScaleInverseVolume.inverse_volume_without_support`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Localization costs and information growth for exact Gaussian observations*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KernelPotential.Noise.weighted_centered_projection` of [lean/OAI/Probability/GaussianInformation/GaussianInformation/Kernel/NoisyProjection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianInformation/GaussianInformation/Kernel/NoisyProjection.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.KernelPotential.Noise`, with `open MeasureTheory ProbabilityTheory Metric Set`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal`, `open MeasureTheory ProbabilityTheory Metric Set`, `open scoped ENNReal`, `open Projection.Support Projection Reweight EntropySupport DriftTools Sphere`):
--
--   ```lean
--   lemma weighted_centered_projection {d : ℕ} (hd : 16 ≤ d)
--       (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
--       (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
--       (L : ℕ) (hL : H*(9*3^d:ℝ) ≤ 2^L) {η : ℝ} (hη : 0 < η)
--       (u : (Fin (d/16) → Fin d → ℝ) → ℝ) (hu : Measurable u)
--       (hu0 : ∀ X,0 ≤ u X) (hu1 : ∀ X,u X ≤ 1) :
--       (∫ X,u X*(∫ Z,Real.log (1+2^(2*(d/16))*
--         (mixedCubeAverage (centeredRho ν s) η X Z).toReal) ∂gaussianRows (d/16) d)
--         ∂gaussianRows (d/16) d) ≤
--         -(∫ X,u X ∂gaussianRows (d/16) d)*Real.log (∫ X,u X ∂gaussianRows (d/16) d)/(d/16:ℕ)+
--           (∫ X,u X ∂gaussianRows (d/16) d)*(10*(d:ℝ)+Real.log ((L:ℝ)+2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.KernelPotential.Projection.mixedCubeAverage`, `OAI.KernelPotential.Reweight.centeredRho` and `OAI.KernelPotential.Projection.Support.gaussianRows` (definitions bundle `OAIQWRLC001` of this split); `OAI.KernelPotential.Ambient` and `OAI.KernelPotential.sphereProbability` (the published bundle `Def_GaussianInformation_003`).
--
--   **Used by.** The proof of `OAI.KernelPotential.MassPotential.local_energy_bound` of this split imports it.
-- source:
--   OpenAI, Localization costs and information growth for exact Gaussian observations, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianInformation/GaussianInformation/Kernel/NoisyProjection.lean (declaration OAI.KernelPotential.Noise.weighted_centered_projection)

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
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight EntropySupport DriftTools Sphere

lemma weighted_centered_projection {d : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    (L : ℕ) (hL : H*(9*3^d:ℝ) ≤ 2^L) {η : ℝ} (hη : 0 < η)
    (u : (Fin (d/16) → Fin d → ℝ) → ℝ) (hu : Measurable u)
    (hu0 : ∀ X,0 ≤ u X) (hu1 : ∀ X,u X ≤ 1) :
    (∫ X,u X*(∫ Z,Real.log (1+2^(2*(d/16))*
      (mixedCubeAverage (centeredRho ν s) η X Z).toReal) ∂gaussianRows (d/16) d)
      ∂gaussianRows (d/16) d) ≤
      -(∫ X,u X ∂gaussianRows (d/16) d)*Real.log (∫ X,u X ∂gaussianRows (d/16) d)/(d/16:ℕ)+
        (∫ X,u X ∂gaussianRows (d/16) d)*(10*(d:ℝ)+Real.log ((L:ℝ)+2)) := by
  sorry

end KernelPotential.Noise

end OAI
end
