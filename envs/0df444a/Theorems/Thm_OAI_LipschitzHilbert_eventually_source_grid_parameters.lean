-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_eventually_source_grid_parameters
-- name    : OAI.LipschitzHilbert.eventually_source_grid_parameters
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:43:46.791464+00:00
-- url     : https://prove2.me/theorems/19ba8dca-234a-4c8d-a9e1-5ddb53a59ed1
-- title:
--   OAI.LipschitzHilbert.eventually_source_grid_parameters: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.eventually_source_grid_parameters` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourceEitherGrid.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceEitherGrid.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert`, with `open Set MeasureTheory Filter`, `open scoped BigOperators Topology`, `open PhaseCombinatorics`):
--
--   ```lean
--   theorem eventually_source_grid_parameters (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F) :
--       ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 1 ≤ D → 0 < N → Real.log N ≤ 2*L →
--       let p := Real.sqrt L
--       let K := L^C*(1+N^phaseMu D p)
--       let ε := SourceParameters.step L^(-(1/8:ℝ))
--       let θ := SourceParameters.step L^(-(1/16:ℝ))
--       ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
--         (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
--       ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
--       ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
--         (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) → (∑ i, c i/n) ≤ 1 →
--       ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
--         (i₀ : ι) (Aconst freqBound u q : ℝ),
--         0 ≤ Aconst → 0 ≤ freqBound → 0 ≤ u →
--         n^phaseMu D p ≤ K → Aconst*n^phaseMu D p ≤ K →
--         (∀ i, ‖A i‖ ≤ Aconst*c i) → (∀ i, ‖lam i‖ ≤ 1) →
--         (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
--         (∑ i : RemainderIndex i₀, c i/n) ≤ u →
--         (∀ i j, i ≠ j → ¬G i j → ∀ k,
--           1/(grid.width*ε) ≤ |frequency i k-frequency j k|) →
--         (∀ S : Finset ι, (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
--           (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
--         (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
--         freqBound*(grid.width/(grid.branching:ℝ)^level) ≤ F*θ →
--       ∀ (n' : ℝ → ℝ) (c' : ℝ → ι → ℝ) (A' : ℝ → ι → EuclideanSpace ℂ κ)
--         (lam' : ℝ → ι → ℂ),
--         (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
--         (∀ b ∈ grid.root, ∀ i,
--           ‖massPowerScale (n' b) (c' b i) (-(1/p)) (phaseMu D p-1+1/p) • A' b i-
--             diagonalModulation (frequency i)
--               (massPowerScale n (c i) (-(1/p)) (phaseMu D p-1+1/p) • A i) b‖ ≤
--             ε*(c i/n)^(1/p)*(c i)^phaseMu D p) →
--         (∀ b ∈ grid.root, ∀ i,
--           ‖(((n' b)^(phaseMu D p-1):ℝ):ℂ) • (lam' b i • A' b i)-
--             ((n^(phaseMu D p-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
--             ε*K*(c i/n)) →
--         (u < 1/2 → lam i₀ ≠ 0 ∧ 0 ≤ q ∧ q < 1 ∧ q ≤ ε ∧
--           0 ≤ (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ∧
--           (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 1 ∧
--           1-(c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 2*u ∧
--           (∀ b ∈ grid.root, ‖lam' b i₀-lam i₀‖ ≤ q*‖lam i₀‖) ∧
--           (∀ b ∈ grid.root, |(c' b i₀/n' b)^(1-phaseMu D p-1/p)*‖lam' b i₀‖-
--             (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖| ≤ 24*ε*u)) →
--         ∃ Γ : ℝ → ℝ, Measurable Γ ∧
--           Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
--           (∀ b, 0 ≤ Γ b) ∧
--           (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
--           (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
--           ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
--             Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.FiniteLineGrid`, `OAI.LipschitzHilbert.sourcePredictionValue`, `OAI.LipschitzHilbert.FiniteLineGrid.index`, `OAI.LipschitzHilbert.FiniteLineGrid.root` and `OAI.LipschitzHilbert.SourceParameters.step` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.closedNeighborhood`, `OAI.LipschitzHilbert.intervalProbability`, `OAI.LipschitzHilbert.massPowerScale`, `OAI.LipschitzHilbert.orderMass`, `OAI.LipschitzHilbert.radialShrink`, `OAI.LipschitzHilbert.PhaseCombinatorics.RemainderIndex`, `OAI.LipschitzHilbert.PhaseCombinatorics.diagonalModulation` and `OAI.LipschitzHilbert.PhaseCombinatorics.phaseMu` (definitions bundle `OAIQ090A001` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceEitherGrid.lean (declaration OAI.LipschitzHilbert.eventually_source_grid_parameters)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A000
import Definitions.Def_OAIQ090A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_grid_parameters (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 1 ≤ D → 0 < N → Real.log N ≤ 2*L →
    let p := Real.sqrt L
    let K := L^C*(1+N^phaseMu D p)
    let ε := SourceParameters.step L^(-(1/8:ℝ))
    let θ := SourceParameters.step L^(-(1/16:ℝ))
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
    ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
    ∀ (c m : ι → ℝ) (n : ℝ), (∀ i, 0 < c i) → 0 < n →
      (∀ i, orderMass c (closedNeighborhood G i) ≤ m i) → (∑ i, c i/n) ≤ 1 →
    ∀ (frequency : ι → κ → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
      (i₀ : ι) (Aconst freqBound u q : ℝ),
      0 ≤ Aconst → 0 ≤ freqBound → 0 ≤ u →
      n^phaseMu D p ≤ K → Aconst*n^phaseMu D p ≤ K →
      (∀ i, ‖A i‖ ≤ Aconst*c i) → (∀ i, ‖lam i‖ ≤ 1) →
      (∀ i, ‖lam i‖ ≤ (c i/m i)^phaseMu D p) →
      (∑ i : RemainderIndex i₀, c i/n) ≤ u →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*ε) ≤ |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (∀ i ∈ S, radialShrink (2*ε*c i) (A i) ≠ 0 ∨ i = i₀) →
        (S:Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i : RemainderIndex i₀, ∀ k, |frequency i k-frequency i₀ k| ≤ freqBound) →
      freqBound*(grid.width/(grid.branching:ℝ)^level) ≤ F*θ →
    ∀ (n' : ℝ → ℝ) (c' : ℝ → ι → ℝ) (A' : ℝ → ι → EuclideanSpace ℂ κ)
      (lam' : ℝ → ι → ℂ),
      (∀ b ∈ grid.root, 0 < n' b) → (∀ b ∈ grid.root, ∀ i, 0 < c' b i) →
      (∀ b ∈ grid.root, ∀ i,
        ‖massPowerScale (n' b) (c' b i) (-(1/p)) (phaseMu D p-1+1/p) • A' b i-
          diagonalModulation (frequency i)
            (massPowerScale n (c i) (-(1/p)) (phaseMu D p-1+1/p) • A i) b‖ ≤
          ε*(c i/n)^(1/p)*(c i)^phaseMu D p) →
      (∀ b ∈ grid.root, ∀ i,
        ‖(((n' b)^(phaseMu D p-1):ℝ):ℂ) • (lam' b i • A' b i)-
          ((n^(phaseMu D p-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
          ε*K*(c i/n)) →
      (u < 1/2 → lam i₀ ≠ 0 ∧ 0 ≤ q ∧ q < 1 ∧ q ≤ ε ∧
        0 ≤ (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ∧
        (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 1 ∧
        1-(c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖ ≤ 2*u ∧
        (∀ b ∈ grid.root, ‖lam' b i₀-lam i₀‖ ≤ q*‖lam i₀‖) ∧
        (∀ b ∈ grid.root, |(c' b i₀/n' b)^(1-phaseMu D p-1/p)*‖lam' b i₀‖-
          (c i₀/n)^(1-phaseMu D p-1/p)*‖lam i₀‖| ≤ 24*ε*u)) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ b ∈ grid.root, sourcePredictionValue p (phaseMu D p) (n' b) (c' b) (A' b) (lam' b) ≤
          Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  sorry

end LipschitzHilbert

end

end OAI
end
