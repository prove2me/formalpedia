-- Prove2me | Theorems.Thm_OAI_LargePrimeGaps_marked_average_uniform_asymptotic
-- name    : OAI.LargePrimeGaps.marked_average_uniform_asymptotic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T04:53:07.038994+00:00
-- url     : https://prove2.me/theorems/bea12f43-6555-40e7-ba7f-799e93608044
-- title:
--   OAI.LargePrimeGaps.marked_average_uniform_asymptotic: intermediate lemma from OpenAI, Positive lower density of large prime gaps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem344.large_gaps_and_ratio_density`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive lower density of large prime gaps*, OpenAI Math Release, September 25, 2026, result family 26, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LargePrimeGaps.marked_average_uniform_asymptotic` of [lean/OAI/NumberTheory/PrimeGaps/LaplaceTransform.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/LaplaceTransform.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LargePrimeGaps`, with `open Filter`, `open Set Filter MeasureTheory`, `open scoped Topology ContDiff`, `open Asymptotics`, `open Asymptotics`, `open Asymptotics`, `open scoped Classical`, `open scoped ContDiff`):
--
--   ```lean
--   theorem marked_average_uniform_asymptotic (hBV : BombieriVinogradov) {n : ℕ}
--       (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
--       (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
--       (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
--       (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
--       (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
--       (B : Finset (Finset (Fin n))) (hB : ∀ S∈B, S.Nonempty)
--       (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
--       (H : ℕ → ℕ) {D₀ B₀ : ℝ} (hD₀ : 0<D₀)
--       (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ)≤D₀*(Real.log (X:ℝ))^B₀) :
--       ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
--         ∀ᶠ X : ℕ in atTop, ∀ b : Fin n → ℕ,
--         shiftFamily (fun i => (b i:ℤ))=B → ∀ a : ℕ, a≤H X →
--         (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, b i≤D) → a≤D →
--         2*D≤densityCutoff β (Real.log X) →
--         ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ) -
--           (singularSeries (insert (a:ℤ) (Finset.univ.image fun i => (b i:ℤ))):ℂ)*
--             kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
--               (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X
--   ```
--
--   **Definitions.** The statement is written with `OAI.LargePrimeGaps.BombieriVinogradov`, `OAI.LargePrimeGaps.HasBudget`, `OAI.LargePrimeGaps.average`, `OAI.LargePrimeGaps.densityCutoff`, `OAI.LargePrimeGaps.divisorSum`, `OAI.LargePrimeGaps.fourierCoordinateSum`, `OAI.LargePrimeGaps.kernelConstant`, `OAI.LargePrimeGaps.shiftFamily`, `OAI.LargePrimeGaps.singularSeries`, `OAI.LargePrimeGaps.sourceFourier` and `OAI.LargePrimeGaps.theta` (definitions bundle `OAIW2PG000` of this split).
--
--   **Used by.** The proofs of `OAI.LargePrimeGaps.unorderedWeight_external_marked_limit` and `OAI.LargePrimeGaps.unorderedWeight_internal_marked_limit` of this split import it.
-- source:
--   OpenAI, Positive lower density of large prime gaps, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 26; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-lower-density-of-large-prime-gaps-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PrimeGaps/LaplaceTransform.lean (declaration OAI.LargePrimeGaps.marked_average_uniform_asymptotic)

import Mathlib
import Definitions.Def_OAIW2PG000

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem marked_average_uniform_asymptotic (hBV : BombieriVinogradov) {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i, 0≤v i) → |F v|≤M)
    (B : Finset (Finset (Fin n))) (hB : ∀ S∈B, S.Nonempty)
    (t β : ℕ) (hβ : 0<β) (ht : (∑ S∈B, (-1:ℤ)^S.card) = -(t:ℤ))
    (H : ℕ → ℕ) {D₀ B₀ : ℝ} (hD₀ : 0<D₀)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ)≤D₀*(Real.log (X:ℝ))^B₀) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ X : ℕ in atTop, ∀ b : Fin n → ℕ,
      shiftFamily (fun i => (b i:ℤ))=B → ∀ a : ℕ, a≤H X →
      (∀ i, b i≠a) → ∀ D : ℕ, (∀ i, b i≤D) → a≤D →
      2*D≤densityCutoff β (Real.log X) →
      ‖(Real.log X:ℂ)^t*(average X (fun m => divisorSum X F m b*theta (m+a)):ℂ) -
        (singularSeries (insert (a:ℤ) (Finset.univ.image fun i => (b i:ℤ))):ℂ)*
          kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
            (fun v => (F v.ofLp:ℂ)) hF hFs) B‖ ≤ E X := by
  sorry

open Topology

open scoped Convolution ContDiff Pointwise

end LargePrimeGaps

end OAI
end
