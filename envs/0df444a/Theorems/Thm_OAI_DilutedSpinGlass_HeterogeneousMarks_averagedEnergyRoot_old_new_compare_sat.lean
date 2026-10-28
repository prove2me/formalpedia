-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_HeterogeneousMarks_averagedEnergyRoot_old_new_compare_sat
-- name    : OAI.DilutedSpinGlass.HeterogeneousMarks.averagedEnergyRoot_old_new_compare_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:17:32.773609+00:00
-- url     : https://prove2.me/theorems/52fb36af-7ba8-430a-b33b-cda990eb69e2
-- title:
--   OAI.DilutedSpinGlass.HeterogeneousMarks.averagedEnergyRoot_old_new_compare_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.HeterogeneousMarks.averagedEnergyRoot_old_new_compare` of [lean/OAI/Probability/DilutedSpin/CavitySiteMean.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/CavitySiteMean.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.HeterogeneousMarks`, with `open _root_.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling`, `open scoped NNReal BigOperators`):
--
--   ```lean
--   lemma averagedEnergyRoot_old_new_compare_sat
--       (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
--       (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure ((Fin N → Spin) → ℝ))
--       [IsProbabilityMeasure ρ] (hρ : Integrable id ρ) (r s : ℝ≥0)
--       (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
--       (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
--       (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
--       (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
--       (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
--       {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
--       (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
--       (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
--       |(∫ E,∫ v,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
--           (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ) (liftOldEnergy E+v)
--           ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
--             (μ.prod (finiteUniform (Fin q → Fin N)))) ∂ρ)-
--         (∫ E,cavityPoissonValue μ ξ theta field
--           (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
--             (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)|≤2*D*s/(N+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Interaction`, `OAI.DilutedSpinGlass.InteractionSample` and `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.cavityPoissonValue`, `OAI.DilutedSpinGlass.compoundPoisson`, `OAI.DilutedSpinGlass.finiteUniform`, `OAI.DilutedSpinGlass.liftOldEnergy`, `OAI.DilutedSpinGlass.newPotential`, `OAI.DilutedSpinGlass.PhysicalRoot.averagedEnergyRoot` and `OAI.DilutedSpinGlass.PhysicalRoot.locatedFactor` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion_rate_bound_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/CavitySiteMean.lean (declaration OAI.DilutedSpinGlass.HeterogeneousMarks.averagedEnergyRoot_old_new_compare)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma averagedEnergyRoot_old_new_compare_sat
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure ((Fin N → Spin) → ℝ))
    [IsProbabilityMeasure ρ] (hρ : Integrable id ρ) (r s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |(∫ E,∫ v,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ) (liftOldEnergy E+v)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))) ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)|≤2*D*s/(N+1) := by
  sorry

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end
