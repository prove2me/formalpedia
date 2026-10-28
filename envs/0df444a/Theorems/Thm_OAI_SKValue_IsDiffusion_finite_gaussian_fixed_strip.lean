-- Prove2me | Theorems.Thm_OAI_SKValue_IsDiffusion_finite_gaussian_fixed_strip
-- name    : OAI.SKValue.IsDiffusion.finite_gaussian_fixed_strip
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:47:44.54688+00:00
-- url     : https://prove2.me/theorems/79ef3a91-1c90-4d66-900b-c3262e04ffbf
-- title:
--   OAI.SKValue.IsDiffusion.finite_gaussian_fixed_strip: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.IsDiffusion.finite_gaussian_fixed_strip` of [lean/OAI/Probability/SKValue/SKValue/Processes/FiniteGaussianFixedStrip.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Processes/FiniteGaussianFixedStrip.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology ENNReal NNReal`, `open Filter Set`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`, `open MeasureTheory Set Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Set Filter Finset`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   lemma IsDiffusion.finite_gaussian_fixed_strip {W : BrownianSpace} {γ : OrderParameter}
--       {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {T K L D Lu La : ℝ}
--       (hT : 0<T) (hT1 : T<1) (hg : GradientStrip T γ.coeff (gradient W γ) K L)
--       (hD : 0≤D) (hLu : 0≤Lu) (hLa : 0≤La)
--       (ha : ∀ t∈Icc (0 : ℝ) T, ∀ x, |curvature W γ t x|≤D)
--       (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
--         |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|))
--       (haLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
--         |curvature W γ s x-curvature W γ t y|≤La*(|s-t|+|x-y|))
--       (hmom : ∀ t∈Icc (0 : ℝ) T, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
--       (∀ᶠ N in atTop, ∀ j<N, 0<normalizer W γ T N j) ∧
--       Tendsto (shiftedCoefficientSum W γ T) atTop
--         (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.GradientStrip` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.IsDiffusion`, `OAI.SKValue.OrderParameter`, `OAI.SKValue.curvature`, `OAI.SKValue.gradient`, `OAI.SKValue.normalizer` and `OAI.SKValue.shiftedCoefficientSum` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.value_consequences` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Processes/FiniteGaussianFixedStrip.lean (declaration OAI.SKValue.IsDiffusion.finite_gaussian_fixed_strip)

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000

section

attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

lemma IsDiffusion.finite_gaussian_fixed_strip {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {T K L D Lu La : ℝ}
    (hT : 0<T) (hT1 : T<1) (hg : GradientStrip T γ.coeff (gradient W γ) K L)
    (hD : 0≤D) (hLu : 0≤Lu) (hLa : 0≤La)
    (ha : ∀ t∈Icc (0 : ℝ) T, ∀ x, |curvature W γ t x|≤D)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|))
    (haLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |curvature W γ s x-curvature W γ t y|≤La*(|s-t|+|x-y|))
    (hmom : ∀ t∈Icc (0 : ℝ) T, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
    (∀ᶠ N in atTop, ∀ j<N, 0<normalizer W γ T N j) ∧
    Tendsto (shiftedCoefficientSum W γ T) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)) := by
  sorry

end SKValue

end

end OAI
end
