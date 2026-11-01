-- Prove2me | Theorems.Thm_OAI_JointDickman_geometric_singularSeries_error_jd
-- name    : OAI.JointDickman.geometric_singularSeries_error_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:32:20.938043+00:00
-- url     : https://prove2.me/theorems/82861428-e640-445e-84fd-6e0869d7f7ec
-- title:
--   OAI.JointDickman.geometric_singularSeries_error_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.geometric_singularSeries_error` of [lean/OAI/NumberTheory/JointDickman/Amplification/GeometricSeriesError.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/GeometricSeriesError.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`, `open scoped Topology SchwartzMap`):
--
--   ```lean
--   theorem geometric_singularSeries_error_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput)
--       {t L U : ℝ} (ht : 0 < t) (hLU : L ≤ U)
--       (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
--       {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
--       (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
--         ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, j*Q ≤ auxiliaryCutoff B →
--         ∀ S : Finset ℤ, ∀ β D : ℝ, 0 ≤ D → ∀ d : ℤ → ℝ,
--         (∀ k ∈ S, |d k| ≤ D) → ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
--         (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
--         ‖((B : ℂ)/j)*∑ k ∈ S, (d k : ℂ)*
--           (sampledEndpointKernel m B j Q (geometricHistogramWindow m B t L U k)
--             g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w-
--           (singularSeries j : ℂ)*sampledEndpointLogKernel m B (geometricHistogramWindow m B t L U k)
--             g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w)‖ ≤
--           (D*C)*(((j : ℝ)/j.totient)/j)*singularSeriesTail (Q+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryCutoff`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.geometricHistogramWindow`, `OAI.JointDickman.sampledEndpointKernel`, `OAI.JointDickman.singularSeries`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.singularSeriesTail` (definitions bundle `OAIQ083J002` of this split); `OAI.JointDickman.sampledEndpointLogKernel` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.bounded_box_coarse_comparison_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/GeometricSeriesError.lean (declaration OAI.JointDickman.geometric_singularSeries_error)

import Mathlib
import Definitions.Def_OAIQ083J003

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem geometric_singularSeries_error_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {t L U : ℝ} (ht : 0 < t) (hLU : L ≤ U)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, j*Q ≤ auxiliaryCutoff B →
      ∀ S : Finset ℤ, ∀ β D : ℝ, 0 ≤ D → ∀ d : ℤ → ℝ,
      (∀ k ∈ S, |d k| ≤ D) → ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ‖((B : ℂ)/j)*∑ k ∈ S, (d k : ℂ)*
        (sampledEndpointKernel m B j Q (geometricHistogramWindow m B t L U k)
          g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w-
        (singularSeries j : ℂ)*sampledEndpointLogKernel m B (geometricHistogramWindow m B t L U k)
          g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w)‖ ≤
        (D*C)*(((j : ℝ)/j.totient)/j)*singularSeriesTail (Q+1) := by
  sorry

end JointDickman

end OAI
end
