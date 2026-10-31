-- Prove2me | Theorems.Thm_OAI_SKRatio_Calculus_ratio_cutoff_of_static_inputs
-- name    : OAI.SKRatio.Calculus.ratio_cutoff_of_static_inputs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:25:40.063966+00:00
-- url     : https://prove2.me/theorems/85e4781a-1746-4d2a-9079-460b443db6fa
-- title:
--   OAI.SKRatio.Calculus.ratio_cutoff_of_static_inputs: intermediate lemma from OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKRatio.Calculus.ratio_cutoff_of_static_inputs` of [lean/OAI/Probability/SKRatio/FiniteChain/StaticReduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/FiniteChain/StaticReduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKRatio.Calculus`, with `open scoped BigOperators Topology Matrix`, `open MeasureTheory Filter`):
--
--   ```lean
--   theorem ratio_cutoff_of_static_inputs (β ε η : ℝ)
--       (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
--       (G : ∀ n : ℕ, Set (Disorder n))
--       (bad : ∀ n, Disorder n → Set (Spin n)) {κ A χ γ K : ℝ}
--       (hκ : 0 < κ) (hA : 0 ≤ A) (hχ : 0 < χ) (hγ : 0 < γ) (hK : 0 < K)
--       (hG : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0))
--       (hnorm : ∀ n, ∀ g ∈ G n, euclideanOpNorm (coupling g) ≤ K)
--       (hgap : ∀ n, ∀ g ∈ G n, ∀ f : Observables n,
--         γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
--       (hmlsi : ∀ n, ∀ g ∈ G n, ∀ F : Observables n,
--         (∀ y, 0 < F y) → FiniteLaw.mean (mass g 0) F = 1 →
--         χ*FiniteLaw.entropy (mass g 0) F ≤
--           -stationaryInner g (generator (coupling g) F) (fun y => Real.log (F y)))
--       (hsmall : ∀ n, ∀ g ∈ G n, FiniteLaw.mean (mass g 0)
--         (fun y => if y ∈ bad n g then 1 else 0) ≤ Real.exp (-κ*n))
--       (hgradient : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ y,
--         (∑ i, 2*halfDiff i f y*halfDiff i (generator (coupling g) f) y) -
--           generator (coupling g) (unweightedGradient f) y ≤
--             (-κ + if y ∈ bad n g then A else 0)*unweightedGradient f y) :
--       Tendsto
--         (fun n : ℕ => disorderLaw β n
--           {g : Disorder n | 1+η <
--             (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
--         atTop (𝓝 0) ∧
--       (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKRatio.Calculus.Observables`, `OAI.SKRatio.Calculus.euclideanOpNorm`, `OAI.SKRatio.Calculus.generator`, `OAI.SKRatio.Calculus.halfDiff`, `OAI.SKRatio.Calculus.stationaryEnergy`, `OAI.SKRatio.Calculus.stationaryInner`, `OAI.SKRatio.Calculus.unweightedGradient` and `OAI.SKRatio.FiniteLaw.mean` (definitions bundle `OAIQ024S000` of this split); `OAI.SKRatio.FiniteLaw.entropy` and `OAI.SKRatio.FiniteLaw.variance` (definitions bundle `OAIQ024S009` of this split); `OAI.SKRatio.Disorder`, `OAI.SKRatio.Edge`, `OAI.SKRatio.Spin`, `OAI.SKRatio.coupling`, `OAI.SKRatio.disorderLaw`, `OAI.SKRatio.mass` and `OAI.SKRatio.mixingTime` (the published bundle `Def_SKRatio`).
--
--   **Used by.** The proof of `OAI.SKRatio.Planted.ratio_cutoff_of_planted_form` of this split imports it.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/FiniteChain/StaticReduction.lean (declaration OAI.SKRatio.Calculus.ratio_cutoff_of_static_inputs)

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S009

section

attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

theorem ratio_cutoff_of_static_inputs (β ε η : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A χ γ K : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hχ : 0 < χ) (hγ : 0 < γ) (hK : 0 < K)
    (hG : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0))
    (hnorm : ∀ n, ∀ g ∈ G n, euclideanOpNorm (coupling g) ≤ K)
    (hgap : ∀ n, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hmlsi : ∀ n, ∀ g ∈ G n, ∀ F : Observables n,
      (∀ y, 0 < F y) → FiniteLaw.mean (mass g 0) F = 1 →
      χ*FiniteLaw.entropy (mass g 0) F ≤
        -stationaryInner g (generator (coupling g) F) (fun y => Real.log (F y)))
    (hsmall : ∀ n, ∀ g ∈ G n, FiniteLaw.mean (mass g 0)
      (fun y => if y ∈ bad n g then 1 else 0) ≤ Real.exp (-κ*n))
    (hgradient : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ y,
      (∑ i, 2*halfDiff i f y*halfDiff i (generator (coupling g) f) y) -
        generator (coupling g) (unweightedGradient f) y ≤
          (-κ + if y ∈ bad n g then A else 0)*unweightedGradient f y) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  sorry

end SKRatio.Calculus

end
end

end OAI
end
