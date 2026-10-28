-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavity_proxy_expected_lower
-- name    : OAI.SphericalPerceptronFreeEnergy.cavity_proxy_expected_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:07:14.880995+00:00
-- url     : https://prove2.me/theorems/d7a98d4a-433c-4655-bed3-982802c23493
-- title:
--   OAI.SphericalPerceptronFreeEnergy.cavity_proxy_expected_lower: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.cavity_proxy_expected_lower` of [lean/OAI/Probability/Perceptron/Cavity/CavityOldExpectation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityOldExpectation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory`, `open scoped Topology BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma cavity_proxy_expected_lower (n k M d : ℕ) (f : Jet3)
--       (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
--       (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
--       (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0) (v : ℕ→ℝ) :
--       cavityBulkFullLog k d n M f v+bulkExpectedLog n M f.f v-cavityOldError n k M d f h1 h2 h3≤
--         ∫ p,cavityProxyLog n (k+1) M d f v p ∂cavityProxyLaw n (k+1) M d
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.BulkDisorder`, `OAI.SphericalPerceptronFreeEnergy.BulkMark`, `OAI.SphericalPerceptronFreeEnergy.CavityProxyRandom`, `OAI.SphericalPerceptronFreeEnergy.EnrichedIndex`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.bulkDegree`, `OAI.SphericalPerceptronFreeEnergy.bulkExpectedLog`, `OAI.SphericalPerceptronFreeEnergy.cavityBulkFullLog`, `OAI.SphericalPerceptronFreeEnergy.cavityOldError`, `OAI.SphericalPerceptronFreeEnergy.cavityProxyLaw`, `OAI.SphericalPerceptronFreeEnergy.cavityProxyLog`, `OAI.SphericalPerceptronFreeEnergy.cavityShell` and `OAI.SphericalPerceptronFreeEnergy.cavitySphereLaw` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.Spin` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.cavity_original_increment_error` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityOldExpectation.lean (declaration OAI.SphericalPerceptronFreeEnergy.cavity_proxy_expected_lower)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_proxy_expected_lower (n k M d : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0) (v : ℕ→ℝ) :
    cavityBulkFullLog k d n M f v+bulkExpectedLog n M f.f v-cavityOldError n k M d f h1 h2 h3≤
      ∫ p,cavityProxyLog n (k+1) M d f v p ∂cavityProxyLaw n (k+1) M d := by
  sorry

end SphericalPerceptronFreeEnergy

end

end OAI
end
