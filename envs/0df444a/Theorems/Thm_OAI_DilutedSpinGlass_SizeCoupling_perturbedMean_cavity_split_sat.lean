-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_SizeCoupling_perturbedMean_cavity_split_sat
-- name    : OAI.DilutedSpinGlass.SizeCoupling.perturbedMean_cavity_split_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:20:08.681915+00:00
-- url     : https://prove2.me/theorems/c34c0c4a-0c34-4d44-8d8c-41fa33ff1cd8
-- title:
--   OAI.DilutedSpinGlass.SizeCoupling.perturbedMean_cavity_split_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.SizeCoupling.perturbedMean_cavity_split` of [lean/OAI/Probability/DilutedSpin/PhysicalCavitySplit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/PhysicalCavitySplit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.SizeCoupling`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower PhysicalRoot`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   lemma perturbedMean_cavity_split_sat
--       (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
--       (ν : Measure I) [IsProbabilityMeasure ν] (α s : ℝ≥0)
--       (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
--       (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
--       (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
--       (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
--       {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
--       (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
--       (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
--       |perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (α*(N+1)) s -
--         ((N+1:ℕ)*Real.log 2 + ∫ E,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
--           (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ) E
--           ∂(compoundPoisson (reservoirRate α q N)
--             (Measure.map (fun z : X × (Fin (q+1) → Fin N) =>
--               indexedPotential theta (z.1,fun i => (z.2 i).succ))
--               (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
--           compoundPoisson (oneNewRate α q N)
--             (Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
--               indexedPotential theta (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
--               (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N)))))))| ≤ C*cavityBadRate α q N
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Interaction`, `OAI.DilutedSpinGlass.InteractionSample` and `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.cavityBadRate`, `OAI.DilutedSpinGlass.compoundPoisson`, `OAI.DilutedSpinGlass.finiteUniform`, `OAI.DilutedSpinGlass.oneNewRate`, `OAI.DilutedSpinGlass.reservoirRate`, `OAI.DilutedSpinGlass.PhysicalRoot.averagedEnergyRoot`, `OAI.DilutedSpinGlass.PhysicalRoot.indexedPotential`, `OAI.DilutedSpinGlass.PhysicalRoot.locatedFactor` and `OAI.DilutedSpinGlass.SizeCoupling.perturbedMean` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/PhysicalCavitySplit.lean (declaration OAI.DilutedSpinGlass.SizeCoupling.perturbedMean_cavity_split)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma perturbedMean_cavity_split_sat
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (α s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |perturbedMean (N := N+1) μ ξ ν theta field Q m ψ (α*(N+1)) s -
      ((N+1:ℕ)*Real.log 2 + ∫ E,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ) E
        ∂(compoundPoisson (reservoirRate α q N)
          (Measure.map (fun z : X × (Fin (q+1) → Fin N) =>
            indexedPotential theta (z.1,fun i => (z.2 i).succ))
            (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) ∗
        compoundPoisson (oneNewRate α q N)
          (Measure.map (fun z : X × (Fin (q+1) × (Fin q → Fin N)) =>
            indexedPotential theta (z.1,z.2.1.insertNth 0 (fun i => (z.2.2 i).succ)))
            (μ.prod (finiteUniform (Fin (q+1) × (Fin q → Fin N)))))))| ≤ C*cavityBadRate α q N := by
  sorry

end DilutedSpinGlass.SizeCoupling

end

end OAI
end
