-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_canonical_phase_triple_smallBall
-- name    : OAI.YauCounterexamples.canonical_phase_triple_smallBall
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:34:18.562762+00:00
-- url     : https://prove2.me/theorems/879157d3-d81d-46ac-a21b-a36894a74316
-- title:
--   OAI.YauCounterexamples.canonical_phase_triple_smallBall: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.canonical_phase_triple_smallBall` of [lean/OAI/Geometry/SmoothYau/Estimates/CanonicalPhaseTripleSmallBall.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/CanonicalPhaseTripleSmallBall.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open scoped Topology`, `open Set Filter Manifold Bundle MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Matrix`, `open scoped Topology Matrix.Norms.Elementwise`, `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`, `open Set Filter MeasureTheory ProbabilityTheory Matrix`, `open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem canonical_phase_triple_smallBall {X : Type*} [TopologicalSpace X] [CompactSpace X]
--       (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (b₀ : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
--       (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb₀ : ∀ p i, ContDiff ℝ ∞ (b₀ p i))
--       (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
--       (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
--       (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
--       (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b₀ q.1 i) q.2))
--       (φ : X → PhaseSpace → ℝ)
--       (hφ0 : Continuous (fun p => φ p 0))
--       (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
--       (F : X → (Fin 3 → ℝ) → ℂ) (hF : ∀ p, ContDiff ℝ ∞ (F p))
--       (hF0 : ∀ p, F p 0 = (φ p 0 : ℂ))
--       (hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
--       (B C κ M η : ℝ) (hM : 1 ≤ M) (hη : 0 < η)
--       (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
--       ∃ r₀ > 0, ∃ c₀ > 0, ∃ ε > 0,
--         ∀ p (n δ : ℝ), 1 ≤ n → 0 < δ → δ < ε → δ^2 = 1/n →
--         ∀ a ν b c d : PhaseSpace, ‖a‖ ≤ M → ‖ν‖ = 1 →
--           inner ℝ ν b = 0 → inner ℝ ν c = 0 →
--           ‖b‖^2 = 1+‖a‖^2 → ‖c‖^2 = 1+‖a‖^2 →
--           ‖b‖ ≤ M → ‖c‖ ≤ M → η ≤ transverseAngleSq b c →
--         let z := ![complexPhaseVector a b,complexPhaseVector a c,
--           complexPhaseVector (a+δ • ν) d]
--         ∀ Q : Fin 3 → ComplexPhaseMatrix,
--           (∀ ℓ, ‖z ℓ‖ ≤ B) → (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) →
--           (∀ ℓ, PhaseMatrixValid (actualHessianForm (φ p)) (z ℓ) κ C (Q ℓ)) →
--         ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
--         ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*(F p x).re) →
--         let W := Real.exp (n*(F p x).re)+R
--         let U := fun ℓ => canonicalCutoffWave (g p) (b₀ p) (φ p 0 : ℂ) (z ℓ) (Q ℓ) ζ m D n
--         ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
--           (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
--         (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
--           {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
--             Metric.closedBall 0 r} ≤
--         ENNReal.ofReal (Real.sqrt η/2*δ*(c₀/2*(n^6)⁻¹)^4)⁻¹*(ENNReal.ofReal (2*r))^4
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.ComplexPhaseMatrix` and `OAI.YauCounterexamples.PhaseSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.complexPhaseVector`, `OAI.YauCounterexamples.complexRealResponse` and `OAI.YauCounterexamples.complexWaveJet` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.PhaseMatrixValid`, `OAI.YauCounterexamples.actualHessianForm` and `OAI.YauCounterexamples.transverseAngleSq` (definitions bundle `OAIQ070A006` of this split); `OAI.YauCounterexamples.canonicalCutoffWave` (definitions bundle `OAIQ070A007` of this split).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_compact_profile_canonical_smallBall_uniform_orders` and `OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/CanonicalPhaseTripleSmallBall.lean (declaration OAI.YauCounterexamples.canonical_phase_triple_smallBall)

import Mathlib
import Definitions.Def_OAIQ070A006
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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise

theorem canonical_phase_triple_smallBall {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b₀ : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb₀ : ∀ p i, ContDiff ℝ ∞ (b₀ p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b₀ q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ)
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (F : X → (Fin 3 → ℝ) → ℂ) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hF0 : ∀ p, F p 0 = (φ p 0 : ℂ))
    (hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (B C κ M η : ℝ) (hM : 1 ≤ M) (hη : 0 < η)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    ∃ r₀ > 0, ∃ c₀ > 0, ∃ ε > 0,
      ∀ p (n δ : ℝ), 1 ≤ n → 0 < δ → δ < ε → δ^2 = 1/n →
      ∀ a ν b c d : PhaseSpace, ‖a‖ ≤ M → ‖ν‖ = 1 →
        inner ℝ ν b = 0 → inner ℝ ν c = 0 →
        ‖b‖^2 = 1+‖a‖^2 → ‖c‖^2 = 1+‖a‖^2 →
        ‖b‖ ≤ M → ‖c‖ ≤ M → η ≤ transverseAngleSq b c →
      let z := ![complexPhaseVector a b,complexPhaseVector a c,
        complexPhaseVector (a+δ • ν) d]
      ∀ Q : Fin 3 → ComplexPhaseMatrix,
        (∀ ℓ, ‖z ℓ‖ ≤ B) → (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) →
        (∀ ℓ, PhaseMatrixValid (actualHessianForm (φ p)) (z ℓ) κ C (Q ℓ)) →
      ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
      ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*(F p x).re) →
      let W := Real.exp (n*(F p x).re)+R
      let U := fun ℓ => canonicalCutoffWave (g p) (b₀ p) (φ p 0 : ℂ) (z ℓ) (Q ℓ) ζ m D n
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤
      ENNReal.ofReal (Real.sqrt η/2*δ*(c₀/2*(n^6)⁻¹)^4)⁻¹*(ENNReal.ofReal (2*r))^4 := by
  sorry

end YauCounterexamples
end

end OAI
end
