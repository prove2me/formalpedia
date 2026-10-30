-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_exists_source_supported_grid_prediction
-- name    : OAI.LipschitzHilbert.exists_source_supported_grid_prediction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:53:09.391569+00:00
-- url     : https://prove2.me/theorems/586b29fe-93bf-4a36-b19a-07c6f6160686
-- title:
--   OAI.LipschitzHilbert.exists_source_supported_grid_prediction: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.exists_source_supported_grid_prediction` of [lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedGrid.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedGrid.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert`, with `open Set MeasureTheory`, `open scoped BigOperators`, `open PhaseCombinatorics`):
--
--   ```lean
--   theorem exists_source_supported_grid_prediction :
--       ∃ C L0 : ℝ, 1 ≤ C ∧ ∀ L : ℝ, L0 ≤ L →
--         ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
--         (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
--         ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
--         ∀ (w m : ι → ℝ), (∀ i, 0 < w i) →
--         (∀ i, orderMass w (closedNeighborhood G i) ≤ m i) →
--         ∀ (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
--           (lam : ι → ℂ) (i₀ : ι) (D p K u freqBound θ : ℝ),
--         1 ≤ D → 4 ≤ p →
--         (∀ i j, i ≠ j → ¬G i j → ∀ k,
--           1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) ≤
--             |frequency i k-frequency j k|) →
--         (∀ S : Finset ι, (∀ i ∈ S, X i ≠ 0 ∨ i = i₀) →
--           (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
--         (∀ i, 0 ≤ l i) → (∑ i, l i) ≤ 1 →
--         (∀ i, ‖lam i‖ ≤ (w i/m i)^phaseMu D p) →
--         0 ≤ K → 0 ≤ u → 0 ≤ freqBound →
--         (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lam D p i‖) ≤ K*u →
--         (∀ i : RemainderIndex i₀, ∀ j, |frequency i j-frequency i₀ j| ≤ freqBound) →
--         0 ≤ θ → θ ≤ 1 →
--         ∃ Γ : ℝ → ℝ, Measurable Γ ∧
--           Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
--           (∀ t, 0 ≤ Γ t) ∧
--           (∫ t, Γ t ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
--           (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
--           ∀ t ∈ grid.root, (1-θ)*graphPredictionValue frequency l X lam D p t+θ ≤
--             Real.exp ((4*C*SourceParameters.step L^(-(1/16:ℝ))*p*K+
--               p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ t
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.FiniteLineGrid`, `OAI.LipschitzHilbert.FiniteLineGrid.index`, `OAI.LipschitzHilbert.FiniteLineGrid.root` and `OAI.LipschitzHilbert.SourceParameters.step` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.closedNeighborhood`, `OAI.LipschitzHilbert.intervalProbability`, `OAI.LipschitzHilbert.orderMass`, `OAI.LipschitzHilbert.predictionCoefficients`, `OAI.LipschitzHilbert.PhaseCombinatorics.RemainderIndex` and `OAI.LipschitzHilbert.PhaseCombinatorics.phaseMu` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.graphPredictionValue` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.eventually_source_grid_parameters` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedGrid.lean (declaration OAI.LipschitzHilbert.exists_source_supported_grid_prediction)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem exists_source_supported_grid_prediction :
    ∃ C L0 : ℝ, 1 ≤ C ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
      ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
      ∀ (w m : ι → ℝ), (∀ i, 0 < w i) →
      (∀ i, orderMass w (closedNeighborhood G i) ≤ m i) →
      ∀ (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
        (lam : ι → ℂ) (i₀ : ι) (D p K u freqBound θ : ℝ),
      1 ≤ D → 4 ≤ p →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) ≤
          |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (∀ i ∈ S, X i ≠ 0 ∨ i = i₀) →
        (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i, 0 ≤ l i) → (∑ i, l i) ≤ 1 →
      (∀ i, ‖lam i‖ ≤ (w i/m i)^phaseMu D p) →
      0 ≤ K → 0 ≤ u → 0 ≤ freqBound →
      (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lam D p i‖) ≤ K*u →
      (∀ i : RemainderIndex i₀, ∀ j, |frequency i j-frequency i₀ j| ≤ freqBound) →
      0 ≤ θ → θ ≤ 1 →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ t, 0 ≤ Γ t) ∧
        (∫ t, Γ t ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ t ∈ grid.root, (1-θ)*graphPredictionValue frequency l X lam D p t+θ ≤
          Real.exp ((4*C*SourceParameters.step L^(-(1/16:ℝ))*p*K+
            p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ t := by
  sorry

end LipschitzHilbert

end

end OAI
end
