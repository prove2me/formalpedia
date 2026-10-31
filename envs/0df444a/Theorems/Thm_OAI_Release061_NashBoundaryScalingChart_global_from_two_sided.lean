-- Prove2me | Theorems.Thm_OAI_Release061_NashBoundaryScalingChart_global_from_two_sided
-- name    : OAI.Release061.NashBoundaryScalingChart.global_from_two_sided
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:53:37.132483+00:00
-- url     : https://prove2.me/theorems/6dd4827c-0721-43cd-8b31-e7a116ce83fd
-- title:
--   OAI.Release061.NashBoundaryScalingChart.global_from_two_sided: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.NashBoundaryScalingChart.global_from_two_sided` of [lean/OAI/Analysis/SymmetricDomains/GlobalTwoSided.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/GlobalTwoSided.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061.NashBoundaryScalingChart`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Topology Metric`, `open scoped Classical`):
--
--   ```lean
--   theorem global_from_two_sided (s : NashBoundaryScalingChart c x)
--       (hgood : c.GoodAt x) (hcut : s.HasCutoffs)
--       (hUV : U ⊆ V) (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
--       (hconn : IsConnected U) (hbounded : Bornology.IsBounded U) (hsmooth : IsSmooth U)
--       [LocallyCompactSpace U] (Γ : Type*) [Group Γ] [TopologicalSpace Γ]
--       [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
--       [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
--       (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
--       (Ω : Set (Affine N)) (hΩV : Ω ⊆ V)
--       (hΩo : IsOpen ((Subtype.val : V → Affine N) ⁻¹' Ω)) (hpΩ : q x ∈ Ω)
--       (hfΩ : MapsTo s.forward s.offsets.source Ω)
--       (hgS : MapsTo s.backward Ω s.offsets.source)
--       (hfg : ∀ y ∈ Ω, s.forward (s.backward y)=y)
--       (h : Fin s.normalDim → Affine N → ℂ)
--       (hh : ∀ i, Differentiable ℂ (h i)) (hh0 : ∀ i, h i (q x)=1)
--       (hb : ∀ i y, y ∈ U → ‖h i y‖ ≤ 1)
--       (i₀ : Fin s.normalDim)
--       (hpeak : ∀ y ∈ U, ‖h i₀ y‖ ≤ Real.exp (-(‖y-q x‖^2)))
--       (β : Fin s.normalDim → Fin s.normalDim → ℝ) (hβ : LinearIndependent ℝ β)
--       (hder : ∀ i z, fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0 z =
--         Complex.I*∑ j, (β i j : ℂ)*z.2 j)
--       (O : Set (Affine s.tangentDim × Affine s.normalDim)) (hO : IsOpen O)
--       (w : Affine s.normalDim) (hw : (0,w) ∈ O)
--       (hcover : ∀ K : Set (Affine s.tangentDim × Affine s.normalDim),
--         IsCompact K → K ⊆ O → ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ s.domain t)
--       (hexclude : ∀ z ∉ O, ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
--         ∃ a : ℕ → Affine s.tangentDim × Affine s.normalDim,
--           Tendsto a atTop (𝓝 z) ∧ ∀ᶠ j in atTop, a j ∉ s.domain (t j)) :
--       Nonempty (Biholomorph U (connectedComponentIn
--         ((affineProductCoordinates s.tangentDim s.normalDim) '' O)
--         ((affineProductCoordinates s.tangentDim s.normalDim) (0,w))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.affineProductCoordinates` (definitions bundle `OAIQ025S000` of this split); `OAI.Release061.NashBoundaryChart`, `OAI.Release061.NashBoundaryScalingChart`, `OAI.Release061.NashBoundaryChart.GoodAt`, `OAI.Release061.NashBoundaryScalingChart.HasCutoffs`, `OAI.Release061.NashBoundaryScalingChart.backward`, `OAI.Release061.NashBoundaryScalingChart.forward`, `OAI.Release061.NashNormalCoordinates` and `OAI.Release061.ProjectionNashChart` (definitions bundle `OAIQ025S001` of this split); `OAI.Release061.NashBoundaryScalingChart.domain` (definitions bundle `OAIQ025S003` of this split); `OAI.Release061.Affine`, `OAI.Release061.Biholomorph`, `OAI.Release061.HolomorphicOnSubset` and `OAI.Release061.IsSmooth` (the published bundle `Def_SymmetricDomains`).
--
--   **Used by.** The proof of `OAI.Release061.original_supported_hermitian_model` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/GlobalTwoSided.lean (declaration OAI.Release061.NashBoundaryScalingChart.global_from_two_sided)

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003

section

attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem global_from_two_sided (s : NashBoundaryScalingChart c x)
    (hgood : c.GoodAt x) (hcut : s.HasCutoffs)
    (hUV : U ⊆ V) (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hconn : IsConnected U) (hbounded : Bornology.IsBounded U) (hsmooth : IsSmooth U)
    [LocallyCompactSpace U] (Γ : Type*) [Group Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
    (Ω : Set (Affine N)) (hΩV : Ω ⊆ V)
    (hΩo : IsOpen ((Subtype.val : V → Affine N) ⁻¹' Ω)) (hpΩ : q x ∈ Ω)
    (hfΩ : MapsTo s.forward s.offsets.source Ω)
    (hgS : MapsTo s.backward Ω s.offsets.source)
    (hfg : ∀ y ∈ Ω, s.forward (s.backward y)=y)
    (h : Fin s.normalDim → Affine N → ℂ)
    (hh : ∀ i, Differentiable ℂ (h i)) (hh0 : ∀ i, h i (q x)=1)
    (hb : ∀ i y, y ∈ U → ‖h i y‖ ≤ 1)
    (i₀ : Fin s.normalDim)
    (hpeak : ∀ y ∈ U, ‖h i₀ y‖ ≤ Real.exp (-(‖y-q x‖^2)))
    (β : Fin s.normalDim → Fin s.normalDim → ℝ) (hβ : LinearIndependent ℝ β)
    (hder : ∀ i z, fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0 z =
      Complex.I*∑ j, (β i j : ℂ)*z.2 j)
    (O : Set (Affine s.tangentDim × Affine s.normalDim)) (hO : IsOpen O)
    (w : Affine s.normalDim) (hw : (0,w) ∈ O)
    (hcover : ∀ K : Set (Affine s.tangentDim × Affine s.normalDim),
      IsCompact K → K ⊆ O → ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ s.domain t)
    (hexclude : ∀ z ∉ O, ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
      ∃ a : ℕ → Affine s.tangentDim × Affine s.normalDim,
        Tendsto a atTop (𝓝 z) ∧ ∀ᶠ j in atTop, a j ∉ s.domain (t j)) :
    Nonempty (Biholomorph U (connectedComponentIn
      ((affineProductCoordinates s.tangentDim s.normalDim) '' O)
      ((affineProductCoordinates s.tangentDim s.normalDim) (0,w)))) := by
  sorry

end NashBoundaryScalingChart
end Release061

end

end OAI
end
