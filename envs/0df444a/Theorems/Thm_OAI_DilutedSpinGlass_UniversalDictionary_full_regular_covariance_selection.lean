-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_full_regular_covariance_selection
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.full_regular_covariance_selection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T07:56:30.995371+00:00
-- url     : https://prove2.me/theorems/11dab0aa-d67c-4561-babd-09575f324a02
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.full_regular_covariance_selection: intermediate lemma from OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DilutedSpinGlass.mezard_parisi`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mézard–Parisi formula for diluted spin glasses (result family 221)*, OpenAI Math Release, September 23, 2026, result family 221, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.full_regular_covariance_selection` of [lean/OAI/Probability/DilutedSpin/DilutedSpin/FullRegularSelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/FullRegularSelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir`, `open ReducedTopology Filter Set`, `open scoped NNReal BigOperators Topology`):
--
--   ```lean
--   theorem full_regular_covariance_selection (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
--       (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ|≤C)
--       (hh : ∀ᵐ h ∂M.field.toMeasure, |h|≤H)
--       (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
--       (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
--       {ε : ℝ} (hε : 0<ε) :
--       ∃ (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ),
--         (∀ L, StrictMono (Ns L)) ∧
--         (∀ L n i, us L n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
--         (∀ L n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns L n) (us L n)≤
--           liminf (pressure M) atTop+ε) ∧
--         (∀ L, FullShapeControl M C H L (Ns L) (us L)) ∧
--         (∀ S η, 0<η → Tendsto (fun L => physicalShapeLimsup M C H L (Ns L) (us L) S η) atTop (𝓝 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.ReducedTopology`, `OAI.DilutedSpinGlass.probeHigh`, `OAI.DilutedSpinGlass.probeLow`, `OAI.DilutedSpinGlass.ConcreteReservoir.increment`, `OAI.DilutedSpinGlass.UniversalDictionary.Alphabet`, `OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec`, `OAI.DilutedSpinGlass.UniversalDictionary.Table`, `OAI.DilutedSpinGlass.UniversalDictionary.anchor`, `OAI.DilutedSpinGlass.UniversalDictionary.direction`, `OAI.DilutedSpinGlass.UniversalDictionary.gridExponents`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalShapeLimsup`, `OAI.DilutedSpinGlass.UniversalDictionary.prior`, `OAI.DilutedSpinGlass.UniversalDictionary.specMeasurable` and `OAI.DilutedSpinGlass.UniversalDictionary.weights` (definitions bundle `OAIQ041D000` of this split); `OAI.DilutedSpinGlass.Interaction`, `OAI.DilutedSpinGlass.InteractionSample`, `OAI.DilutedSpinGlass.Model`, `OAI.DilutedSpinGlass.Spin` and `OAI.DilutedSpinGlass.pressure` (the published bundle `Def_DilutedSpin`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.mezard_parisi` of this split imports it.
-- source:
--   OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 221; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/FullRegularSelection.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.full_regular_covariance_selection)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

theorem full_regular_covariance_selection (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ|≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h|≤H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ),
      (∀ L, StrictMono (Ns L)) ∧
      (∀ L n i, us L n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ L n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns L n) (us L n)≤
        liminf (pressure M) atTop+ε) ∧
      (∀ L, FullShapeControl M C H L (Ns L) (us L)) ∧
      (∀ S η, 0<η → Tendsto (fun L => physicalShapeLimsup M C H L (Ns L) (us L) S η) atTop (𝓝 0)) := by
  sorry

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end
