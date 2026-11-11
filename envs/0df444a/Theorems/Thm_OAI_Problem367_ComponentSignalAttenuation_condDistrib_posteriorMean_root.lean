-- Prove2me | Theorems.Thm_OAI_Problem367_ComponentSignalAttenuation_condDistrib_posteriorMean_root
-- name    : OAI.Problem367.ComponentSignalAttenuation.condDistrib_posteriorMean_root
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:27.482767+00:00
-- url     : https://prove2.me/theorems/fcd7d91f-fcc5-4d61-87d1-26c02d06ee37
-- title:
--   OAI.Problem367.ComponentSignalAttenuation.condDistrib_posteriorMean_root: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.ComponentSignalAttenuation.condDistrib_posteriorMean_root` of [lean/OAI/Probability/FreeIsing/Trees/RootComponentAttenuation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Trees/RootComponentAttenuation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.ComponentSignalAttenuation`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open PlantedSymmetry`):
--
--   ```lean
--   theorem condDistrib_posteriorMean_root
--       {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
--       (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
--       (c : Fin d) (t : ℝ≥0) (a : IsingSpin) :
--       condDistrib (posteriorMean μ c t) (fun z => z.1 (RootedBroadcast.root d))
--         (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) a =
--           linearSignalTilt (posteriorLaw μ c t) id (spinSign a * theta)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.spinSign` and `OAI.Problem367.RootedBroadcast.root` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.linearSignalTilt`, `OAI.Problem367.PlantedSymmetry.gaussianNoiseLaw` and `OAI.Problem367.PlantedSymmetry.gaussianNoiseLaw_probability` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.ComponentSignalAttenuation.posteriorLaw` and `OAI.Problem367.ComponentSignalAttenuation.posteriorMean` (definitions bundle `Q243FI003` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le` and `OAI.Problem367.measure_gaussian_inward_restricted_path_average_ge_le_double_exp` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Trees/RootComponentAttenuation.lean (declaration OAI.Problem367.ComponentSignalAttenuation.condDistrib_posteriorMean_root)

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI003

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

namespace ComponentSignalAttenuation

open PlantedSymmetry

local instance rootComponentAttenuationMeasurableSingletonIsingSpin_r284695_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance rootComponentAttenuationNonemptyIsingSpin_r284695_1 : Nonempty IsingSpin := ⟨.neg⟩
theorem condDistrib_posteriorMean_root
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (c : Fin d) (t : ℝ≥0) (a : IsingSpin) :
    condDistrib (posteriorMean μ c t) (fun z => z.1 (RootedBroadcast.root d))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) a =
        linearSignalTilt (posteriorLaw μ c t) id (spinSign a * theta) := by
  sorry

end ComponentSignalAttenuation

end Problem367

end

end OAI
end
