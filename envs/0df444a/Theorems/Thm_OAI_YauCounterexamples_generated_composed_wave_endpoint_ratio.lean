-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_generated_composed_wave_endpoint_ratio
-- name    : OAI.YauCounterexamples.generated_composed_wave_endpoint_ratio
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:43:07.518008+00:00
-- url     : https://prove2.me/theorems/69670be8-5f53-4132-81c5-d5180ef9f2e2
-- title:
--   OAI.YauCounterexamples.generated_composed_wave_endpoint_ratio: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.generated_composed_wave_endpoint_ratio` of [lean/OAI/Geometry/SmoothYau/Smoothness/UniformJetBoundsFiberComp.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/UniformJetBoundsFiberComp.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem generated_composed_wave_endpoint_ratio
--       (partition : X → P) (hπ : Continuous partition)
--       (ψ : P × E → (Fin 3 → ℝ)) (hψ : ContDiff ℝ ∞ ψ)
--       (hψ0 : ∀ p, ψ (partition p,0) = 0)
--       (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
--       (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
--       (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
--       (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
--       (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
--       (s : X → ℂ) (hs : Continuous s) (z : X → Fin 3 → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
--       (Q : X → ComplexPhaseMatrix) (hQ : ∀ i j, Continuous (fun p => Q p i j))
--       (hsym : ∀ p i j, Q p i j = Q p j i)
--       (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
--       (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
--       let K := 2*D+3*m+6
--       let J := D+m+1
--       let S := fun p t => realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)) (ψ (partition p,t))
--       let U := fun p n t => canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n (ψ (partition p,t))
--       ∃ r₀ > 0, ∃ C > 0, ∀ p (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → 0 ≤ δ →
--         ∀ x y : E, ‖x‖ ≤ r → ‖y‖ ≤ r → n*‖y-x‖ ≤ 1 →
--         ∀ L : E →L[ℝ] ℂ, ‖fderiv ℝ (S p) 0-L‖ ≤ δ → C*r+δ ≤ 1/2 →
--         ‖U p n y-Complex.exp ((n : ℂ)*L (y-x))*U p n x‖ ≤
--           (10*(C*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*U p n x‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ComplexPhaseMatrix` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.realPolyEval` and `OAI.YauCounterexamples.smoothPhasePolynomial` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.canonicalCutoffWave` (definitions bundle `OAIQ070A007` of this split).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_normal_family_composed_endpoint_ratio` and `OAI.YauCounterexamples.uniform_coordinate_packets_with_endpoint_ratios_supported` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Smoothness/UniformJetBoundsFiberComp.lean (declaration OAI.YauCounterexamples.generated_composed_wave_endpoint_ratio)

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

open Set Filter
open scoped Topology ContDiff
variable {X P E F : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem generated_composed_wave_endpoint_ratio
    (partition : X → P) (hπ : Continuous partition)
    (ψ : P × E → (Fin 3 → ℝ)) (hψ : ContDiff ℝ ∞ ψ)
    (hψ0 : ∀ p, ψ (partition p,0) = 0)
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → Fin 3 → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (Q : X → ComplexPhaseMatrix) (hQ : ∀ i j, Continuous (fun p => Q p i j))
    (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    let K := 2*D+3*m+6
    let J := D+m+1
    let S := fun p t => realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)) (ψ (partition p,t))
    let U := fun p n t => canonicalCutoffWave (g p) (b p) (s p) (z p) (Q p) ζ m D n (ψ (partition p,t))
    ∃ r₀ > 0, ∃ C > 0, ∀ p (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → 0 ≤ δ →
      ∀ x y : E, ‖x‖ ≤ r → ‖y‖ ≤ r → n*‖y-x‖ ≤ 1 →
      ∀ L : E →L[ℝ] ℂ, ‖fderiv ℝ (S p) 0-L‖ ≤ δ → C*r+δ ≤ 1/2 →
      ‖U p n y-Complex.exp ((n : ℂ)*L (y-x))*U p n x‖ ≤
        (10*(C*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*U p n x‖ := by
  sorry

end YauCounterexamples
end

end OAI
end
