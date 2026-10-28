-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_PhysicalRoot_spin_selected_concentration
-- name    : OAI.DilutedSpinGlass.PhysicalRoot.spin_selected_concentration
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T07:54:04.906934+00:00
-- url     : https://prove2.me/theorems/766a77d5-6ff3-43a7-a254-5391db59222e
-- title:
--   OAI.DilutedSpinGlass.PhysicalRoot.spin_selected_concentration: intermediate lemma from OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DilutedSpinGlass.mezard_parisi`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mézard–Parisi formula for diluted spin glasses (result family 221)*, OpenAI Math Release, September 23, 2026, result family 221, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.PhysicalRoot.spin_selected_concentration` of [lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalSelectedConcentration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalSelectedConcentration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.PhysicalRoot`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks Set`, `open scoped NNReal ENNReal BigOperators`):
--
--   ```lean
--   theorem spin_selected_concentration
--       (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
--       (ξ : Measure Y) [IsProbabilityMeasure ξ] (r s : ℝ≥0)
--       (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
--       (hVm : ∀ σ, Measurable (fun x => V x σ)) (hhm : Measurable field)
--       {C H c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
--       (hV : ∀ x σ, |V x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
--       (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
--       (hm : ∀ j, c ≤ m j)
--       (sel : I → Bool)
--       (fixed D E : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
--       (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
--       (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
--       {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
--       (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
--       let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
--       let base := fun h k (x : RootPath X k) z => energy V field h k x (KernelTower.terminalState L z)
--       (∫ u in a..b, fullSelectedError (fun _ : Fin N => ξ) μ ν r s T Q m base sel fixed D E t u)/(b-a) ≤
--         Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ))/(b-a)+
--         4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+2*H^2*N)/ρ+
--         12*ρ*(s:ℝ)/(b-a)+Real.sqrt s
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.RootPath`, `OAI.DilutedSpinGlass.FiniteLaw.uniform`, `OAI.DilutedSpinGlass.HeterogeneousMarks.fullSelectedError`, `OAI.DilutedSpinGlass.KernelTower.terminalState`, `OAI.DilutedSpinGlass.KernelTower.terminalTower` and `OAI.DilutedSpinGlass.PhysicalRoot.energy` (definitions bundle `OAIQ041D000` of this split); `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.ConcreteReservoir.scoreError_tendsto` of this split imports it.
-- source:
--   OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 221; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalSelectedConcentration.lean (declaration OAI.DilutedSpinGlass.PhysicalRoot.spin_selected_concentration)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks Set
open scoped NNReal ENNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)] {N L : ℕ}

theorem spin_selected_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hVm : ∀ σ, Measurable (fun x => V x σ)) (hhm : Measurable field)
    {C H c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hV : ∀ x σ, |V x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j, c ≤ m j)
    (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
    let base := fun h k (x : RootPath X k) z => energy V field h k x (KernelTower.terminalState L z)
    (∫ u in a..b, fullSelectedError (fun _ : Fin N => ξ) μ ν r s T Q m base sel fixed D E t u)/(b-a) ≤
      Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ))/(b-a)+
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+2*H^2*N)/ρ+
      12*ρ*(s:ℝ)/(b-a)+Real.sqrt s := by
  sorry

end DilutedSpinGlass.PhysicalRoot
end

end

end OAI
end
