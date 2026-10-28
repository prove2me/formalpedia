-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_generated_wave_uniform_jets
-- name    : OAI.YauCounterexamples.generated_wave_uniform_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:44:49.179638+00:00
-- url     : https://prove2.me/theorems/8dcf800b-468d-470c-83d5-5d92098f54c4
-- title:
--   OAI.YauCounterexamples.generated_wave_uniform_jets: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.generated_wave_uniform_jets` of [lean/OAI/Geometry/SmoothYau/Smoothness/SmoothFiniteWaveSum.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SmoothFiniteWaveSum.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem generated_wave_uniform_jets
--       (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
--       (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
--       (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
--       (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
--       (hgc : ∀ i j k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
--       (hbc : ∀ i k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
--       (s : X → ℂ) (hs : Continuous s) (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
--       (hz₀ : ∀ p, z p ≠ 0) (Q : X → σ → σ → ℂ)
--       (hQ : ∀ i j, Continuous (fun p => Q p i j)) (hsym : ∀ p i j, Q p i j = Q p j i)
--       (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
--       (K J : ℕ) (hK : 1 ≤ K) {P : Set X} (hP : IsCompact P)
--       {B : Set (σ → ℝ)} (hB : IsCompact B) :
--       let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
--       let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
--       UniformJetBounds (fun p => realPolyEval (S p)) P B ∧
--       (∀ j, UniformJetBounds (fun p x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x) P B) ∧
--       (∀ j, UniformJetBounds (fun p => polynomialWaveRemainder (g p) (b p) (S p) (V p) j) P B) ∧
--       (∀ j, UniformJetBounds (fun p => smoothPolynomialLaplacian (g p) (b p) (V p j)) P B) ∧
--       (∀ j, UniformJetBounds (fun p => realPolyEval (V p j)) P B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.UniformJetBounds`, `OAI.YauCounterexamples.realPolyEval`, `OAI.YauCounterexamples.smoothPhasePolynomial`, `OAI.YauCounterexamples.smoothPolynomialLaplacian` and `OAI.YauCounterexamples.uniformSmoothWaveAmplitudes` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.polynomialWaveRemainder` and `OAI.YauCounterexamples.smoothEikonalResidual` (definitions bundle `OAIQ070A007` of this split).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_admissible_cutoff_wave_localized_derivatives`, `OAI.YauCounterexamples.admissible_cutoff_wave_residual`, `OAI.YauCounterexamples.generated_composed_wave_endpoint_ratio`, `OAI_YauCounterexamples_generated_cutoff_wave_residual_estimate`, `OAI.YauCounterexamples.generated_cutoff_waves_near_center` and `OAI.YauCounterexamples.normal_family_wave_localized_estimates` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/SmoothFiniteWaveSum.lean (declaration OAI.YauCounterexamples.generated_wave_uniform_jets)

import Mathlib
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*}

variable {σ : Type*} [Fintype σ] [DecidableEq σ] [TopologicalSpace X]

theorem generated_wave_uniform_jets
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (hz₀ : ∀ p, z p ≠ 0) (Q : X → σ → σ → ℂ)
    (hQ : ∀ i j, Continuous (fun p => Q p i j)) (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (K J : ℕ) (hK : 1 ≤ K) {P : Set X} (hP : IsCompact P)
    {B : Set (σ → ℝ)} (hB : IsCompact B) :
    let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
    let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
    UniformJetBounds (fun p => realPolyEval (S p)) P B ∧
    (∀ j, UniformJetBounds (fun p x => smoothEikonalResidual (g p) (S p) x * realPolyEval (V p j) x) P B) ∧
    (∀ j, UniformJetBounds (fun p => polynomialWaveRemainder (g p) (b p) (S p) (V p) j) P B) ∧
    (∀ j, UniformJetBounds (fun p => smoothPolynomialLaplacian (g p) (b p) (V p j)) P B) ∧
    (∀ j, UniformJetBounds (fun p => realPolyEval (V p j)) P B) := by
  sorry
end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end
