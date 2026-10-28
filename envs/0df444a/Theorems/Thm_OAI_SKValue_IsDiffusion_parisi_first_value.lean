-- Prove2me | Theorems.Thm_OAI_SKValue_IsDiffusion_parisi_first_value
-- name    : OAI.SKValue.IsDiffusion.parisi_first_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:48:51.098435+00:00
-- url     : https://prove2.me/theorems/75c38d67-c1f1-42cc-a2dd-04dbb8682150
-- title:
--   OAI.SKValue.IsDiffusion.parisi_first_value: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.IsDiffusion.parisi_first_value` of [lean/OAI/Probability/SKValue/SKValue/Evolution/TimeWeightedIntervalIntegrable.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Evolution/TimeWeightedIntervalIntegrable.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology ENNReal NNReal`, `open Filter Set`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`, `open MeasureTheory Set Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Set Filter Finset`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem IsDiffusion.parisi_first_value {W : BrownianSpace} {γ : OrderParameter}
--       {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
--       (hstrips : ∀ T : ℝ, 0<T → T<1 → ∃ K L Kg Lg Lu : ℝ,
--         ValueStrip T γ.coeff (phi W γ) K L ∧
--         GradientStrip T γ.coeff (gradient W γ) Kg Lg ∧ 0≤Lu ∧
--         ∀ t∈Icc (0 : ℝ) T, ∀ s∈Icc (0 : ℝ) T, ∀ x y,
--           |gradient W γ s y-gradient W γ t x|≤Lu*(|s-t|+|y-x|))
--       (hmoment : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
--       parisi W γ=(∫ ω, |X 1 ω| ∂W.μ)-∫ t in (0 : ℝ)..1, t*γ.coeff t
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.GradientStrip` and `OAI.SKValue.ValueStrip` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.IsDiffusion`, `OAI.SKValue.OrderParameter`, `OAI.SKValue.gradient`, `OAI.SKValue.parisi` and `OAI.SKValue.phi` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.IsDiffusion.parisi_value_assembly` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Evolution/TimeWeightedIntervalIntegrable.lean (declaration OAI.SKValue.IsDiffusion.parisi_first_value)

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

theorem IsDiffusion.parisi_first_value {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hstrips : ∀ T : ℝ, 0<T → T<1 → ∃ K L Kg Lg Lu : ℝ,
      ValueStrip T γ.coeff (phi W γ) K L ∧
      GradientStrip T γ.coeff (gradient W γ) Kg Lg ∧ 0≤Lu ∧
      ∀ t∈Icc (0 : ℝ) T, ∀ s∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s y-gradient W γ t x|≤Lu*(|s-t|+|y-x|))
    (hmoment : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    parisi W γ=(∫ ω, |X 1 ω| ∂W.μ)-∫ t in (0 : ℝ)..1, t*γ.coeff t := by
  sorry

end SKValue

end

end OAI
end
