-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_localized_packet_sign_probability
-- name    : OAI.YauCounterexamples.localized_packet_sign_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:43:51.065399+00:00
-- url     : https://prove2.me/theorems/1f214a2c-8a94-4bc1-8b87-ee7629f8f03c
-- title:
--   OAI.YauCounterexamples.localized_packet_sign_probability: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.localized_packet_sign_probability` of [lean/OAI/Geometry/SmoothYau/Estimates/LocalizedPacketSignProbability.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/LocalizedPacketSignProbability.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology ENNReal RealInnerProductSpace`):
--
--   ```lean
--   theorem localized_packet_sign_probability {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
--       ∃ p > 0, ∀ (I : Type) [Fintype I] [DecidableEq I]
--         (φ : NormalWaveSpace → ℝ) (K : Set NormalWaveSpace)
--         (q : I → NormalWaveSpace) (β : I → NormalWaveSpace →L[ℝ] ℝ)
--         (U : I → NormalWaveSpace → ℂ) (b : NormalWaveSpace → ℝ)
--         (H Hs ε ℓ t T c M δ : ℝ) (x : NormalWaveSpace),
--         0 ≤ H → 0 ≤ Hs → 0 < ε → ε ≤ 1 → 1 ≤ ℓ → 2 ≤ t →
--         0 < T → 0 < c → 0 ≤ M → 0 < δ → δ ≤ 1/16 → δ ≤ κ/96 →
--         M*(2/t) ≤ δ/2 → (∀ i, q i ∈ K) → x ∈ K →
--         (∀ j, packetAxisShift x (t^4) ε ℓ j ∈ K) →
--         (∀ y ∈ K, ∃ i, t^4*‖y-q i‖ ≤ 1) →
--         (∀ q ∈ K, ∀ y, ‖y-q‖ ≤ 1 → ‖fderiv ℝ φ y‖ ≤ H ∧ |φ y-φ q| ≤ H*‖y-q‖) →
--         (∀ j, Real.exp (-Hs) ≤ Real.exp ((ε/ℓ)*fderiv ℝ φ x
--           (EuclideanSpace.basisFun (Fin 3) ℝ j))) →
--         (∀ i, U i (q i) = Complex.exp (((t^4 : ℝ) : ℂ)*(φ (q i) : ℂ))) →
--         (∀ i y, ‖U i y‖ ≤ T*Real.exp (t^4*φ y)*Real.exp (-c*t^4*‖y-q i‖^2)) →
--         (∀ i a y, ‖a-q i‖ ≤ 2/t → ‖y-q i‖ ≤ 2/t → t^4*‖y-a‖ ≤ 1 →
--           ‖U i y-(Real.exp (t^4*fderiv ℝ φ a (y-a)) : ℂ)*
--             Complex.exp (((t^4*β i (y-a) : ℝ) : ℂ)*Complex.I)*U i a‖ ≤
--           (M*(2/t))*‖(Real.exp (t^4*fderiv ℝ φ a (y-a)) : ℂ)*
--             Complex.exp (((t^4*β i (y-a) : ℝ) : ℂ)*Complex.I)*U i a‖) →
--         (∀ i, ‖x-q i‖ ≤ t⁻¹ →
--           (∀ j, |ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ 1) ∧
--           κ ≤ ∑ j, (ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j))^2) →
--         (Fintype.card I : ℝ)*T*Real.exp H*Real.exp (-c*t^2/4) ≤
--           (δ/2)*Real.exp (-Hs)*(Real.exp (-2*H)/2) →
--         (∀ y ∈ K, |b y| ≤ (Real.exp (-2*H)/2)*Real.exp (t^4*φ y)) →
--         ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
--           {γ | (b x+complexGaussianRealValue (fun i => U i x) γ)*
--             (b (packetAxisShift x (t^4) ε ℓ j)+
--               complexGaussianRealValue (fun i => U i (packetAxisShift x (t^4) ε ℓ j)) γ) < 0}
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.NormalWaveSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.complexGaussianRealValue` (definitions bundle `OAIQ070A003` of this split); `OAI.YauCounterexamples.packetAxisShift` (definitions bundle `OAIQ070A007` of this split).
--
--   **Used by.** The proof of `OAI.YauCounterexamples.compact_metric_packet_sign_gain` of this split imports it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/Estimates/LocalizedPacketSignProbability.lean (declaration OAI.YauCounterexamples.localized_packet_sign_probability)

import Mathlib
import Definitions.Def_OAIQ070A007

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

theorem localized_packet_sign_probability {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ p > 0, ∀ (I : Type) [Fintype I] [DecidableEq I]
      (φ : NormalWaveSpace → ℝ) (K : Set NormalWaveSpace)
      (q : I → NormalWaveSpace) (β : I → NormalWaveSpace →L[ℝ] ℝ)
      (U : I → NormalWaveSpace → ℂ) (b : NormalWaveSpace → ℝ)
      (H Hs ε ℓ t T c M δ : ℝ) (x : NormalWaveSpace),
      0 ≤ H → 0 ≤ Hs → 0 < ε → ε ≤ 1 → 1 ≤ ℓ → 2 ≤ t →
      0 < T → 0 < c → 0 ≤ M → 0 < δ → δ ≤ 1/16 → δ ≤ κ/96 →
      M*(2/t) ≤ δ/2 → (∀ i, q i ∈ K) → x ∈ K →
      (∀ j, packetAxisShift x (t^4) ε ℓ j ∈ K) →
      (∀ y ∈ K, ∃ i, t^4*‖y-q i‖ ≤ 1) →
      (∀ q ∈ K, ∀ y, ‖y-q‖ ≤ 1 → ‖fderiv ℝ φ y‖ ≤ H ∧ |φ y-φ q| ≤ H*‖y-q‖) →
      (∀ j, Real.exp (-Hs) ≤ Real.exp ((ε/ℓ)*fderiv ℝ φ x
        (EuclideanSpace.basisFun (Fin 3) ℝ j))) →
      (∀ i, U i (q i) = Complex.exp (((t^4 : ℝ) : ℂ)*(φ (q i) : ℂ))) →
      (∀ i y, ‖U i y‖ ≤ T*Real.exp (t^4*φ y)*Real.exp (-c*t^4*‖y-q i‖^2)) →
      (∀ i a y, ‖a-q i‖ ≤ 2/t → ‖y-q i‖ ≤ 2/t → t^4*‖y-a‖ ≤ 1 →
        ‖U i y-(Real.exp (t^4*fderiv ℝ φ a (y-a)) : ℂ)*
          Complex.exp (((t^4*β i (y-a) : ℝ) : ℂ)*Complex.I)*U i a‖ ≤
        (M*(2/t))*‖(Real.exp (t^4*fderiv ℝ φ a (y-a)) : ℂ)*
          Complex.exp (((t^4*β i (y-a) : ℝ) : ℂ)*Complex.I)*U i a‖) →
      (∀ i, ‖x-q i‖ ≤ t⁻¹ →
        (∀ j, |ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ 1) ∧
        κ ≤ ∑ j, (ε/ℓ*β i (EuclideanSpace.basisFun (Fin 3) ℝ j))^2) →
      (Fintype.card I : ℝ)*T*Real.exp H*Real.exp (-c*t^2/4) ≤
        (δ/2)*Real.exp (-Hs)*(Real.exp (-2*H)/2) →
      (∀ y ∈ K, |b y| ≤ (Real.exp (-2*H)/2)*Real.exp (t^4*φ y)) →
      ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (b x+complexGaussianRealValue (fun i => U i x) γ)*
          (b (packetAxisShift x (t^4) ε ℓ j)+
            complexGaussianRealValue (fun i => U i (packetAxisShift x (t^4) ε ℓ j)) γ) < 0} := by
  sorry

end YauCounterexamples
end

end OAI
end
