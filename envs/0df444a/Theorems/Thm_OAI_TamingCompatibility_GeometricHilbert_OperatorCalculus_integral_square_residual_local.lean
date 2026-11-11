-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_OperatorCalculus_integral_square_residual_local
-- name    : OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.integral_square_residual_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:58.198416+00:00
-- url     : https://prove2.me/theorems/f9e6e15d-9483-4d73-855f-68a361df3268
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.integral_square_residual_local: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.integral_square_residual_local` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactExtension.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactExtension.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus`, with `open _root_.MeasureTheory MeasureTheory.Measure Set Filter`, `open scoped ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma integral_square_residual_local {U K : Set V} (hU : IsOpen U)
--       (hK : IsCompact K) (hKU : K ⊆ U)
--       (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
--       (ρ : V → ℝ) (k d r η : V → W)
--       (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U)
--       (hρ : ContDiffOn ℝ ∞ ρ U) (hk : ContDiffOn ℝ ∞ k U)
--       (hd : ContinuousOn d U) (hη : ContDiffOn ℝ ∞ η U)
--       (hks : tsupport k ⊆ K) (hds : Function.support d ⊆ K) (hrs : Function.support r ⊆ K)
--       (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
--       (hres : ∀ x ∈ U, d x + weightedAdjoint e a b ρ (differential e a b k) x = r x) :
--       (∫ x, ρ x * ⟪η x,d x⟫ ∂μ) +
--         (∫ x, ρ x * ⟪differential e a b η x,differential e a b k x⟫ ∂μ) =
--         ∫ x, ρ x * ⟪η x,r x⟫ ∂μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.differential` and `OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.weightedAdjoint` (definitions bundle `OAIQ239Tc004` of this split).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCompactExtension.lean (declaration OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.integral_square_residual_local)

import Mathlib
import Definitions.Def_OAIQ239Tc004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open _root_.MeasureTheory MeasureTheory.Measure Set Filter
open scoped ContDiff Topology RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

variable (μ : Measure V) [IsAddHaarMeasure μ]
lemma integral_square_residual_local {U K : Set V} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (k d r η : V → W)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U)
    (hρ : ContDiffOn ℝ ∞ ρ U) (hk : ContDiffOn ℝ ∞ k U)
    (hd : ContinuousOn d U) (hη : ContDiffOn ℝ ∞ η U)
    (hks : tsupport k ⊆ K) (hds : Function.support d ⊆ K) (hrs : Function.support r ⊆ K)
    (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hres : ∀ x ∈ U, d x + weightedAdjoint e a b ρ (differential e a b k) x = r x) :
    (∫ x, ρ x * ⟪η x,d x⟫ ∂μ) +
      (∫ x, ρ x * ⟪differential e a b η x,differential e a b k x⟫ ∂μ) =
      ∫ x, ρ x * ⟪η x,r x⟫ ∂μ := by
  sorry

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
end
