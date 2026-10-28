-- Prove2me | Theorems.Thm_OAI_Rokhlin_polynomial_cancellation
-- name    : OAI.Rokhlin.polynomial_cancellation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:38:16.26027+00:00
-- url     : https://prove2.me/theorems/e216a9be-b0c2-4ddc-bbe6-eb8c35f80168
-- title:
--   OAI.Rokhlin.polynomial_cancellation: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.polynomial_cancellation` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Foundations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Foundations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin`, with `open MeasureTheory Filter`, `open scoped BigOperators ComplexConjugate`, `open MeasureTheory Filter`, `open scoped BigOperators Topology`, `open MeasureTheory Filter`, `open scoped Topology InnerProductSpace ComplexConjugate`, `open Filter`, `open scoped BigOperators Topology InnerProductSpace`, `open MeasureTheory Filter`, `open scoped BigOperators Topology InnerProductSpace ComplexConjugate`):
--
--   ```lean
--   theorem polynomial_cancellation
--       (htadd : ∀ a b z, t (a + b) z = t b (t a z))
--       (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
--         Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
--       (d : ℕ) (P : ℕ → L) (hP : DifferencePolynomial d P)
--       {F : X → ℂ} (hFm : AEStronglyMeasurable F μ)
--       {C : ℝ} (hC : 0 ≤ C) (hFb : ∀ᵐ z ∂μ, ‖F z‖ ≤ C)
--       (hF0 : ∫ z, F z ∂μ = 0) :
--       Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
--         ‖∫ y, F (t m (x y)) * conj (χ (P m) y) ∂η‖) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.DifferencePolynomial` and `OAI.Rokhlin.ProjectiveCharacters` (definitions bundle `OAIQ3Ro001` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.local_moving_cancellation` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Foundations.lean (declaration OAI.Rokhlin.polynomial_cancellation)

import Mathlib
import Definitions.Def_OAIQ3Ro001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Rokhlin

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

open MeasureTheory Filter
open scoped BigOperators Topology

open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate

open Filter
open scoped BigOperators Topology InnerProductSpace

section

open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate

variable {X Y L : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddCommGroup L]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {η : Measure Y} [IsProbabilityMeasure η]
    (x : Y → X) (hx : MeasurePreserving x η μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    {χ : L → Y → ℂ} (hχ : ProjectiveCharacters η χ)

include hx ht hχ in

theorem polynomial_cancellation
    (htadd : ∀ a b z, t (a + b) z = t b (t a z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (d : ℕ) (P : ℕ → L) (hP : DifferencePolynomial d P)
    {F : X → ℂ} (hFm : AEStronglyMeasurable F μ)
    {C : ℝ} (hC : 0 ≤ C) (hFb : ∀ᵐ z ∂μ, ‖F z‖ ≤ C)
    (hF0 : ∫ z, F z ∂μ = 0) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
      ‖∫ y, F (t m (x y)) * conj (χ (P m) y) ∂η‖) atTop (𝓝 0) := by
  sorry

end

open scoped BigOperators
open Polynomial

open scoped BigOperators

open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

end Rokhlin

end OAI
end
