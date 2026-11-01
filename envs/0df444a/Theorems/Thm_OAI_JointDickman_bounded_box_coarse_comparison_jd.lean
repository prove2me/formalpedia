-- Prove2me | Theorems.Thm_OAI_JointDickman_bounded_box_coarse_comparison_jd
-- name    : OAI.JointDickman.bounded_box_coarse_comparison_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:23:11.0669+00:00
-- url     : https://prove2.me/theorems/d68e3e25-fc3f-46db-bccd-63fdf625379c
-- title:
--   OAI.JointDickman.bounded_box_coarse_comparison_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.bounded_box_coarse_comparison` of [lean/OAI/NumberTheory/JointDickman/Amplification/BoundedBoxCoarse.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/BoundedBoxCoarse.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`, `open scoped Topology SchwartzMap`):
--
--   ```lean
--   theorem bounded_box_coarse_comparison_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput)
--       {D : ℝ} (hD : 0 ≤ D)
--       {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
--       (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
--       {M₁ M₂ D₁ D₂ M₀ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
--       (hM₀ : 0 ≤ M₀)
--       (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
--       (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
--       (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
--       (hwb₀ : ∀ x, |w x| ≤ M₀)
--       (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
--       (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
--    :
--       ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
--         ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
--         ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
--         ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
--         (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
--         ∀ d : ℤ → ℝ, (∀ k ∈ S, |d k| ≤ D) →
--         ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
--         (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
--         let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
--           (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)
--         T*‖geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
--           ((singularSeries j : ℂ)/j)*
--             (cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K : ℂ)‖ ≤
--           ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1)+δ*(T/j)*singularSeries j
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.cellMassBilinear`, `OAI.JointDickman.channelFineCount`, `OAI.JointDickman.coarseLogMass`, `OAI.JointDickman.endpointSpatialWeight`, `OAI.JointDickman.geometricFullArcSum`, `OAI.JointDickman.geometricWindowKernel`, `OAI.JointDickman.singularSeries`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.singularSeriesTail` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proofs of `OAI.JointDickman.amplification_positive_mass_bound_jd` and `OAI.JointDickman.counting_arithmetic_feature_comparison_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/BoundedBoxCoarse.lean (declaration OAI.JointDickman.bounded_box_coarse_comparison)

import Mathlib
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

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

theorem bounded_box_coarse_comparison_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {D : ℝ} (hD : 0 ≤ D)
    {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ D₁ D₂ M₀ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hM₀ : 0 ≤ M₀)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hwb₀ : ∀ x, |w x| ≤ M₀)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
 :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      ∀ d : ℤ → ℝ, (∀ k ∈ S, |d k| ≤ D) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)
      T*‖geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*
          (cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K : ℂ)‖ ≤
        ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1)+δ*(T/j)*singularSeries j := by
  sorry

end JointDickman

end OAI
end
