-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavity_original_increment_error
-- name    : OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:06:40.78391+00:00
-- url     : https://prove2.me/theorems/9e695e32-488a-4d8f-95bb-52c97988b6e0
-- title:
--   OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error` of [lean/OAI/Probability/Perceptron/Cavity/CavityGoodFreshLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityGoodFreshLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma cavity_original_increment_error {α : ℝ} (hα : 0≤α) (k : ℕ) (g : Jet3)
--       (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
--       (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {δ : ℝ} (hδ : 0<δ) :
--       ∀ᶠ n : ℕ in atTop,∀ v : ℕ→ℝ,(∀ p,|v (p+1)|≤2)→
--         Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2-δ+
--           cavityBulkFullLog k (cavityFreshCount α n (k+1)) n (patternCount α (n+1)) g v≤
--         cavityOriginalIncrement α g.f n k v
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.cavityBulkFullLog`, `OAI.SphericalPerceptronFreeEnergy.cavityFreshCount`, `OAI.SphericalPerceptronFreeEnergy.cavityOriginalIncrement`, `OAI.SphericalPerceptronFreeEnergy.cavityShellMass` and `OAI.SphericalPerceptronFreeEnergy.Jet3.dilationMark` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.patternCount` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.cavity_averaged_increment_good` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityGoodFreshLower.lean (declaration OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavity_original_increment_error {α : ℝ} (hα : 0≤α) (k : ℕ) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ n : ℕ in atTop,∀ v : ℕ→ℝ,(∀ p,|v (p+1)|≤2)→
      Real.log (cavityShellMass k)-α*‖g.dilationMark h1‖/2-δ+
        cavityBulkFullLog k (cavityFreshCount α n (k+1)) n (patternCount α (n+1)) g v≤
      cavityOriginalIncrement α g.f n k v := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
