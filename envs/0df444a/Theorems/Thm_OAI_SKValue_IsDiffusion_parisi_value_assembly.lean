-- Prove2me | Theorems.Thm_OAI_SKValue_IsDiffusion_parisi_value_assembly
-- name    : OAI.SKValue.IsDiffusion.parisi_value_assembly
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:48:35.302688+00:00
-- url     : https://prove2.me/theorems/93f9f8f0-6e00-4136-b01e-ba5ea8e8d547
-- title:
--   OAI.SKValue.IsDiffusion.parisi_value_assembly: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.IsDiffusion.parisi_value_assembly` of [lean/OAI/Probability/SKValue/SKValue/Evolution/IntegralPrimitiveTerminal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Evolution/IntegralPrimitiveTerminal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology ENNReal NNReal`, `open Filter Set`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`, `open MeasureTheory Set Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Set Filter Finset`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal`):
--
--   ```lean
--   theorem IsDiffusion.parisi_value_assembly {W : BrownianSpace} {γ : OrderParameter}
--       {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
--       (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t)
--       (hamom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
--       ∃ U : W.Ω → ℝ,
--         Martingale (gradientStopped W γ X U) W.filtration W.μ ∧
--         (∀ᵐ ω ∂W.μ, |U ω|≤1 ∧ (U ω)^2=1 ∧
--           Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
--         Tendsto (fun t ↦ ∫ ω, (gradient W γ t (X t ω)-U ω)^2 ∂W.μ)
--           (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) ∧
--         parisi W γ=(∫ ω, |X 1 ω| ∂W.μ)-∫ t in (0 : ℝ)..1, t*γ.coeff t ∧
--         parisi W γ=∫ ω, U ω*W.B 1 ω ∂W.μ ∧
--         parisi W γ=∫ t in (0 : ℝ)..1, ∫ ω, curvature W γ t (X t ω) ∂W.μ ∧
--         IntervalIntegrable (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) volume 0 1 ∧
--         Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
--           (𝓝[<] (1 : ℝ)) (𝓝 (parisi W γ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.SourceStripRegularity` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.IsDiffusion`, `OAI.SKValue.OrderParameter`, `OAI.SKValue.curvature`, `OAI.SKValue.gradient`, `OAI.SKValue.gradientStopped`, `OAI.SKValue.parisi` and `OAI.SKValue.BrownianSpace.filtration` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.value_consequences` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Evolution/IntegralPrimitiveTerminal.lean (declaration OAI.SKValue.IsDiffusion.parisi_value_assembly)

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
open scoped Topology NNReal

theorem IsDiffusion.parisi_value_assembly {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t)
    (hamom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
    ∃ U : W.Ω → ℝ,
      Martingale (gradientStopped W γ X U) W.filtration W.μ ∧
      (∀ᵐ ω ∂W.μ, |U ω|≤1 ∧ (U ω)^2=1 ∧
        Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
      Tendsto (fun t ↦ ∫ ω, (gradient W γ t (X t ω)-U ω)^2 ∂W.μ)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) ∧
      parisi W γ=(∫ ω, |X 1 ω| ∂W.μ)-∫ t in (0 : ℝ)..1, t*γ.coeff t ∧
      parisi W γ=∫ ω, U ω*W.B 1 ω ∂W.μ ∧
      parisi W γ=∫ t in (0 : ℝ)..1, ∫ ω, curvature W γ t (X t ω) ∂W.μ ∧
      IntervalIntegrable (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) volume 0 1 ∧
      Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
        (𝓝[<] (1 : ℝ)) (𝓝 (parisi W γ)) := by
  sorry

end SKValue

end

end OAI
end
