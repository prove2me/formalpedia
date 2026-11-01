-- Prove2me | Theorems.Thm_OAI_JointDickman_counting_model_energy_mean_proved_jd
-- name    : OAI.JointDickman.counting_model_energy_mean_proved_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:25:10.212256+00:00
-- url     : https://prove2.me/theorems/fe13c278-9fc3-4304-b311-815011d3f312
-- title:
--   OAI.JointDickman.counting_model_energy_mean_proved_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.counting_model_energy_mean_proved` of [lean/OAI/NumberTheory/JointDickman/Counting/CountingModelMeanDischarge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingModelMeanDischarge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter MeasureTheory Classical PublishedInputs`, `open scoped Topology`):
--
--   ```lean
--   theorem counting_model_energy_mean_proved_jd
--       (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
--       (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
--       (hMP : PrimeProductMertensInput)
--       {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
--       (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
--       (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
--       (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
--       (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
--       (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2)) (D : (Fin 4 →₀ ℕ) → ℕ)
--       {η : ℝ} (hη : 0 < η)
--       (A scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (L : ℕ) (τ C : ℝ)
--       (hA : ∀ B, 0 < A B) (hscale : Tendsto scale atTop atTop)
--       (hR : Tendsto R atTop atTop)
--       (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
--       (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B)
--       (hMpos : ∀ᶠ B in atTop, 0 < M B)
--       {V : ℝ} (hV : 0 ≤ V) (hroot : ∀ᶠ B in atTop, independentRootMean B L τ C ≤ V) :
--       ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
--         ∀ (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) →
--         let z := fun k => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ k-μ
--         (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
--           (|(complexEnergy (countingArithmeticKernel singularSeries P m B L
--             (T B) (H B) (M B) u τ C c D (σ u))
--             (fun i => z (u+(i.val+1)))).re|/(M B : ℝ))) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.CharacterDistanceDivergence`, `OAI.JointDickman.binLabel`, `OAI.JointDickman.centeredBinPrefix`, `OAI.JointDickman.complexEnergy`, `OAI.JointDickman.countingArithmeticKernel`, `OAI.JointDickman.independentRootMean`, `OAI.JointDickman.primeBin`, `OAI.JointDickman.singularSeries`, `OAI.JointDickman.squarefreeLeadingConstant`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.finite_graph_centered_mean_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingModelMeanDischarge.lean (declaration OAI.JointDickman.counting_model_energy_mean_proved)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem counting_model_energy_mean_proved_jd
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2)) (D : (Fin 4 →₀ ℕ) → ℕ)
    {η : ℝ} (hη : 0 < η)
    (A scale : ℕ → ℝ) (T H R M : ℕ → ℕ) (L : ℕ) (τ C : ℝ)
    (hA : ∀ B, 0 < A B) (hscale : Tendsto scale atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hRT : Tendsto (fun B => (R B : ℝ)/(T B : ℝ)) atTop (𝓝 0))
    (hvalid : ∀ᶠ B in atTop, 0 < T B ∧ Real.log (T B) ≤ (B : ℝ)/10 ∧ η*T B ≤ H B)
    (hMpos : ∀ᶠ B in atTop, 0 < M B)
    {V : ℝ} (hV : 0 ≤ V) (hroot : ∀ᶠ B in atTop, independentRootMean B L τ C ≤ V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ (σ : ℕ → ℝ), (∀ u, |σ u| ≤ 3) →
      let z := fun k => binLabel (fun j : Fin (J-1) => primeBin (scale n) J (j.val+1)) ζ k-μ
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        (|(complexEnergy (countingArithmeticKernel singularSeries P m B L
          (T B) (H B) (M B) u τ C c D (σ u))
          (fun i => z (u+(i.val+1)))).re|/(M B : ℝ))) < ε := by
  sorry

end JointDickman

end OAI
end
