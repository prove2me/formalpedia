-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_finiteSphericalFieldValue_depth_uniform
-- name    : OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue_depth_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:06:54.566502+00:00
-- url     : https://prove2.me/theorems/503f6e61-169d-4e7a-9984-fac5ffeef473
-- title:
--   OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue_depth_uniform: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue_depth_uniform` of [lean/OAI/Probability/Perceptron/Cavity/CavitySphericalGrid.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavitySphericalGrid.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators`):
--
--   ```lean
--   theorem finiteSphericalFieldValue_depth_uniform (H : ℝ) (hH : 0≤H)
--       (ε : ℝ) (hε : 0<ε) :
--       ∀ᶠ n : ℕ in atTop, ∀ d (w h : Fin (d+1)→ℝ)
--         (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1),
--         Monotone h → 0≤h 0 → h (Fin.last d)≤H →
--         |finiteSphericalFieldValue n d w h-
--           sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)|<ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.finiteSphericalDualValues` and `OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue` (definitions bundle `OAIQ61Pf000` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.cavity_averaged_increment_good` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavitySphericalGrid.lean (declaration OAI.SphericalPerceptronFreeEnergy.finiteSphericalFieldValue_depth_uniform)

import Mathlib
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instCoeFunBoundedFieldForallElemRealTime _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

theorem finiteSphericalFieldValue_depth_uniform (H : ℝ) (hH : 0≤H)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d (w h : Fin (d+1)→ℝ)
      (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1),
      Monotone h → 0≤h 0 → h (Fin.last d)≤H →
      |finiteSphericalFieldValue n d w h-
        sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)|<ε := by
  sorry
end SphericalPerceptronFreeEnergy

end

end OAI
end
