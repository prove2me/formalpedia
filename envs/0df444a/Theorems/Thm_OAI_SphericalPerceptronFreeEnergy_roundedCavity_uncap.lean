-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_roundedCavity_uncap
-- name    : OAI.SphericalPerceptronFreeEnergy.roundedCavity_uncap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:11:11.388093+00:00
-- url     : https://prove2.me/theorems/ba187633-6e5f-4cc3-90f3-be79c6114ee5
-- title:
--   OAI.SphericalPerceptronFreeEnergy.roundedCavity_uncap: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.roundedCavity_uncap` of [lean/OAI/Probability/Perceptron/Cavity/BulkCavityRecursion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkCavityRecursion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction`):
--
--   ```lean
--   theorem roundedCavity_uncap (n d : ℕ) (g : Jet3) (P : Measure BrownianPath)
--       [IsProbabilityMeasure P] (hBrow : IsBrownianReal brownianEval P)
--       (η : Measure Time) [IsProbabilityMeasure η] {B K a : ℝ} (hB : B<1)
--       (ha0 : 0≤a) (haK : a≤K) (j : ℕ) {Λ : ℝ} (hΛ : 1≤Λ) :
--       0 ≤ roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j ∧
--       roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j≤
--         Real.exp (2*((d:ℝ)*‖g.f‖))/Λ*Real.exp (2*(n+1:ℕ)*a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.Jet3` and `OAI.SphericalPerceptronFreeEnergy.roundedCavityLog` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.roundedCavityValue` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.BrownianPath`, `OAI.SphericalPerceptronFreeEnergy.Time`, `OAI.SphericalPerceptronFreeEnergy.brownianEval` and `OAI.SphericalPerceptronFreeEnergy.instMeasurableSpaceBrownianPath` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.cavity_averaged_increment_good` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/BulkCavityRecursion.lean (declaration OAI.SphericalPerceptronFreeEnergy.roundedCavity_uncap)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem roundedCavity_uncap (n d : ℕ) (g : Jet3) (P : Measure BrownianPath)
    [IsProbabilityMeasure P] (hBrow : IsBrownianReal brownianEval P)
    (η : Measure Time) [IsProbabilityMeasure η] {B K a : ℝ} (hB : B<1)
    (ha0 : 0≤a) (haK : a≤K) (j : ℕ) {Λ : ℝ} (hΛ : 1≤Λ) :
    0 ≤ roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j ∧
    roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j≤
      Real.exp (2*((d:ℝ)*‖g.f‖))/Λ*Real.exp (2*(n+1:ℕ)*a) := by
  sorry
end SphericalPerceptronFreeEnergy

end

end OAI
end
