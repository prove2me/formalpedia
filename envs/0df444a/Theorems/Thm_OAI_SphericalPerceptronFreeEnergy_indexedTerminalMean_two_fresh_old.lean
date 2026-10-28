-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_indexedTerminalMean_two_fresh_old
-- name    : OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean_two_fresh_old
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:07:33.424406+00:00
-- url     : https://prove2.me/theorems/4a3da407-b9b6-4a99-a0e1-ab356a15da84
-- title:
--   OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean_two_fresh_old: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean_two_fresh_old` of [lean/OAI/Probability/Perceptron/Variational/SingleRestorationLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/SingleRestorationLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal BigOperators`):
--
--   ```lean
--   lemma indexedTerminalMean_two_fresh_old
--       (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (τ : ProbabilityMeasure U)
--       (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) (π : ProbabilityMeasure V)
--       (st₁ : X×S→X) (st₂ : Y×T→Y) (st₀ : Z×V→Z)
--       (hs₁ : Measurable st₁) (hs₂ : Measurable st₂) (hs₀ : Measurable st₀)
--       (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
--       (H : X→ℝ) (G : Y→ℝ) (J : Z→ℝ) (hH : Measurable H) (hG : Measurable G) (hJ : Measurable J)
--       (hHI : finiteCascadeFractionalIntegrable ν st₁ H n z)
--       (hGI : finiteCascadeFractionalIntegrable ρ st₂ G n z)
--       (hJI : finiteCascadeFractionalIntegrable π st₀ J n z)
--       (x : R→X) (y : Q→Y) (v : U→Z) (hx : Measurable x) (hy : Measurable y) (hv : Measurable v)
--       (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
--       (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D) :
--       let st := fun p : ((X×Y)×Z)×((S×T)×V) =>
--         ((st₁ (p.1.1.1,p.2.1.1),st₂ (p.1.1.2,p.2.1.2)),st₀ (p.1.2,p.2.2))
--       (∫ p, indexedTerminalMean st n (fun p => (H p.1.1+G p.1.2)+J p.2)
--         ((x p.1.1.1,y p.1.1.2),v p.1.2) (fun p => f p.1.1*g p.1.2)
--         (p.2.1,indexedMarksZip n p.2.2)
--         ∂(((μ : Measure R).prod (σ : Measure Q)).prod (τ : Measure U)).prod
--           ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
--             ((indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n)).prod
--               (indexedCascadeMarksLaw π n)))) =
--         (rootPathMean μ x n (fun i => tiltedStateStep ν st₁ (z i)
--             (finiteCascadeShifts ν st₁ n z H i)) f *
--           rootPathMean σ y n (fun i => tiltedStateStep ρ st₂ (z i)
--             (finiteCascadeShifts ρ st₂ n z G i)) g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeBase`, `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeMarks`, `OAI.SphericalPerceptronFreeEnergy.finiteCascadeFractionalIntegrable`, `OAI.SphericalPerceptronFreeEnergy.finiteCascadeShifts`, `OAI.SphericalPerceptronFreeEnergy.indexedCascadeBaseLaw`, `OAI.SphericalPerceptronFreeEnergy.indexedCascadeMarksLaw`, `OAI.SphericalPerceptronFreeEnergy.indexedMarksZip`, `OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean`, `OAI.SphericalPerceptronFreeEnergy.productMarkLaw`, `OAI.SphericalPerceptronFreeEnergy.rootPathMean` and `OAI.SphericalPerceptronFreeEnergy.tiltedStateStep` (definitions bundle `OAIQ61Pf000` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.sourceLabelSingle_witness` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/SingleRestorationLaw.lean (declaration OAI.SphericalPerceptronFreeEnergy.indexedTerminalMean_two_fresh_old)

import Mathlib
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X Y Z R Q U S T V : Type}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace R] [MeasurableSpace Q] [MeasurableSpace U]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace V]
  [Nonempty S] [Nonempty T] [Nonempty V]

lemma indexedTerminalMean_two_fresh_old
    (μ : ProbabilityMeasure R) (σ : ProbabilityMeasure Q) (τ : ProbabilityMeasure U)
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) (π : ProbabilityMeasure V)
    (st₁ : X×S→X) (st₂ : Y×T→Y) (st₀ : Z×V→Z)
    (hs₁ : Measurable st₁) (hs₂ : Measurable st₂) (hs₀ : Measurable st₀)
    (n : ℕ) (z : Fin n→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (H : X→ℝ) (G : Y→ℝ) (J : Z→ℝ) (hH : Measurable H) (hG : Measurable G) (hJ : Measurable J)
    (hHI : finiteCascadeFractionalIntegrable ν st₁ H n z)
    (hGI : finiteCascadeFractionalIntegrable ρ st₂ G n z)
    (hJI : finiteCascadeFractionalIntegrable π st₀ J n z)
    (x : R→X) (y : Q→Y) (v : U→Z) (hx : Measurable x) (hy : Measurable y) (hv : Measurable v)
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D) (hfB : ∀ a, |f a|≤C) (hgB : ∀ b, |g b|≤D) :
    let st := fun p : ((X×Y)×Z)×((S×T)×V) =>
      ((st₁ (p.1.1.1,p.2.1.1),st₂ (p.1.1.2,p.2.1.2)),st₀ (p.1.2,p.2.2))
    (∫ p, indexedTerminalMean st n (fun p => (H p.1.1+G p.1.2)+J p.2)
      ((x p.1.1.1,y p.1.1.2),v p.1.2) (fun p => f p.1.1*g p.1.2)
      (p.2.1,indexedMarksZip n p.2.2)
      ∂(((μ : Measure R).prod (σ : Measure Q)).prod (τ : Measure U)).prod
        ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
          ((indexedCascadeMarksLaw (productMarkLaw ν ρ) n : Measure (IndexedCascadeMarks (S×T) n)).prod
            (indexedCascadeMarksLaw π n)))) =
      (rootPathMean μ x n (fun i => tiltedStateStep ν st₁ (z i)
          (finiteCascadeShifts ν st₁ n z H i)) f *
        rootPathMean σ y n (fun i => tiltedStateStep ρ st₂ (z i)
          (finiteCascadeShifts ρ st₂ n z G i)) g) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
