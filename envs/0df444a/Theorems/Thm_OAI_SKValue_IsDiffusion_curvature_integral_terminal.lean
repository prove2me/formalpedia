-- Prove2me | Theorems.Thm_OAI_SKValue_IsDiffusion_curvature_integral_terminal
-- name    : OAI.SKValue.IsDiffusion.curvature_integral_terminal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T07:47:36.422585+00:00
-- url     : https://prove2.me/theorems/a14cdd65-a02e-4e0c-87e3-c6f4b342d962
-- title:
--   OAI.SKValue.IsDiffusion.curvature_integral_terminal: intermediate lemma from OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKValue.value_consequences`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QAOA attains the SK ground-state energy in the thermodynamic-first limit*, OpenAI Math Release, September 25, 2026, result family 281, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKValue.IsDiffusion.curvature_integral_terminal` of [lean/OAI/Probability/SKValue/SKValue/Control/StripRegularity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Control/StripRegularity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKValue`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology ENNReal NNReal`, `open Filter Set`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`, `open MeasureTheory Set Filter`, `open scoped Topology BigOperators`, `open MeasureTheory Set Filter Finset`, `open scoped Topology BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal`):
--
--   ```lean
--   lemma IsDiffusion.curvature_integral_terminal {W : BrownianSpace} {γ : OrderParameter}
--       {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
--       (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
--       {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
--       (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
--         Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω))) :
--       Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
--         (𝓝[<] (1 : ℝ)) (𝓝 (∫ ω, U ω*W.B 1 ω ∂W.μ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKValue.SourceStripRegularity`, `OAI.SKValue.UnitMomentMartingale`, `OAI.SKValue.terminalTime` and `OAI.SKValue.BrownianSpace.realFiltration` (definitions bundle `OAIQ4Sk000` of this split); `OAI.SKValue.BrownianSpace`, `OAI.SKValue.IsDiffusion`, `OAI.SKValue.OrderParameter`, `OAI.SKValue.curvature` and `OAI.SKValue.gradient` (the published bundle `Def_SKValue`).
--
--   **Used by.** The proof of `OAI.SKValue.IsDiffusion.parisi_value_assembly` of this split imports it.
-- source:
--   OpenAI, QAOA attains the SK ground-state energy in the thermodynamic-first limit, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 281; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026/QAOA-attains-the-SK-ground-state-energy-in-the-thermodynamic-first-limit-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKValue/SKValue/Control/StripRegularity.lean (declaration OAI.SKValue.IsDiffusion.curvature_integral_terminal)

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

lemma IsDiffusion.curvature_integral_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
    {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
    (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω))) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ ω, U ω*W.B 1 ω ∂W.μ)) := by
  sorry

end SKValue

end

end OAI
end
