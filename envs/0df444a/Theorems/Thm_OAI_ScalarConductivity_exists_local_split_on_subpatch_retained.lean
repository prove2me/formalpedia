-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_exists_local_split_on_subpatch_retained
-- name    : OAI.ScalarConductivity.exists_local_split_on_subpatch_retained
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:38:01.551448+00:00
-- url     : https://prove2.me/theorems/dbd407a4-43e8-4f15-990d-89554d3e1177
-- title:
--   OAI.ScalarConductivity.exists_local_split_on_subpatch_retained: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.exists_local_split_on_subpatch_retained` of [lean/OAI/Analysis/Conductivity/Geometry/LocalSplitSubpatchRetained.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Geometry/LocalSplitSubpatchRetained.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open MeasureTheory`, `open scoped ENNReal`, `open Matrix Filter Topology`, `open Set MeasureTheory Filter Topology`, `open scoped BigOperators`, `open Set MeasureTheory Filter Topology`, `open scoped Manifold`, `open Set Filter`, `open scoped Topology`, `open Set Filter MeasureTheory`, `open scoped Topology Manifold ENNReal`, `open Set`, `open Matrix Set MeasureTheory Filter Topology`, `open scoped ENNReal Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem exists_local_split_on_subpatch_retained
--       (μ : Measure Coord3) [μ.IsAddHaarMeasure]
--       (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
--       (A : Coord3 → Symmetric3) {p : Coord3} (hA : ContinuousAt A p)
--       (hD : Function.Surjective (fderiv ℝ u p))
--       (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
--       (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
--       {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
--       (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1 + c * z)
--       (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
--       (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
--       (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
--         (C z).val = (splitJacobian d L c z).det⁻¹ •
--           (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
--       {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
--       (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G)
--       {U : Set Coord3} (hU : IsOpen U) (hpU : p ∈ U) :
--       ∃ (X : OpenPartialHomeomorph Coord3 Coord3) (W : Set Coord3),
--         IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧ W ⊆ X.source ∧
--         ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧
--         ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target ∧
--         ∀ O : Set Coord3, IsOpen O → O ⊆ W →
--         ∀ ε : ℝ, 0 < ε →
--         ∃ (χ : SmoothScalar Coord3) (H : SmoothScalar ℝ) (F : ℝ → Fin 2 → Coord3 → Coord3),
--           HasCompactSupport χ.val ∧ tsupport χ.val ⊆ X '' O ∧
--           (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) ∧
--           (∀ t, -θ ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ 1-θ) ∧
--           (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
--           (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ O ∧ tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
--           (∀ k j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
--             (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
--           ∀ᶠ n : ℕ in atTop, ∃ Y : Coord3 ≃ Coord3,
--             ContDiff ℝ (↑(⊤ : ℕ∞)) Y ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm ∧
--             (∀ x ∉ O, Y x = x) ∧ Y '' O = O ∧
--             (∀ x, Y x = x + (c * (n+1 : ℝ)⁻¹ * localPullback X χ.val x *
--               H.val ((n+1 : ℝ) * L (X x))) • d) ∧
--             μ {x | x ∈ O ∧
--               localPullback X χ.val (Y.symm x) *
--                 (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ -θ ∧
--               localPullback X χ.val (Y.symm x) *
--                 (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ 1-θ} ≤
--               ENNReal.ofReal ε ∧
--             ∀ x ∈ O,
--               let z := localPullback X χ.val x * (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
--               let E := gradientColumns (fderiv ℝ u x)
--               let Ft := (A x).val * E + Matrix.of (fun i j => F (n+1 : ℝ) j x i)
--               let J := operatorMatrix (fderiv ℝ Y x)
--               let At := repairPushed (C z) J E Ft
--               0 < J.det ∧ LinearIndependent ℝ E.col ∧ (z, At) ∈ G ∧
--                 At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.Mat3`, `OAI.ScalarConductivity.SmoothScalar`, `OAI.ScalarConductivity.Symmetric3`, `OAI.ScalarConductivity.gradientColumns`, `OAI.ScalarConductivity.operatorMatrix` and `OAI.ScalarConductivity.smoothDirection` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.localPullback` (definitions bundle `OAIQ059C002` of this split); `OAI.ScalarConductivity.pushFlux`, `OAI.ScalarConductivity.repairPushed` and `OAI.ScalarConductivity.splitJacobian` (definitions bundle `OAIQ059C005` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.fine_global_scalar_tensor_approximation` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Geometry/LocalSplitSubpatchRetained.lean (declaration OAI.ScalarConductivity.exists_local_split_on_subpatch_retained)

import Mathlib
import Definitions.Def_OAIQ059C005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped ENNReal Matrix.Norms.Elementwise
theorem exists_local_split_on_subpatch_retained
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hA : ContinuousAt A p)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1 + c * z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
    (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G)
    {U : Set Coord3} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ (X : OpenPartialHomeomorph Coord3 Coord3) (W : Set Coord3),
      IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧ W ⊆ X.source ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W →
      ∀ ε : ℝ, 0 < ε →
      ∃ (χ : SmoothScalar Coord3) (H : SmoothScalar ℝ) (F : ℝ → Fin 2 → Coord3 → Coord3),
        HasCompactSupport χ.val ∧ tsupport χ.val ⊆ X '' O ∧
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) ∧
        (∀ t, -θ ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ 1-θ) ∧
        (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
        (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ O ∧ tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
        (∀ k j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
          (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
        ∀ᶠ n : ℕ in atTop, ∃ Y : Coord3 ≃ Coord3,
          ContDiff ℝ (↑(⊤ : ℕ∞)) Y ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm ∧
          (∀ x ∉ O, Y x = x) ∧ Y '' O = O ∧
          (∀ x, Y x = x + (c * (n+1 : ℝ)⁻¹ * localPullback X χ.val x *
            H.val ((n+1 : ℝ) * L (X x))) • d) ∧
          μ {x | x ∈ O ∧
            localPullback X χ.val (Y.symm x) *
              (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ -θ ∧
            localPullback X χ.val (Y.symm x) *
              (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ 1-θ} ≤
            ENNReal.ofReal ε ∧
          ∀ x ∈ O,
            let z := localPullback X χ.val x * (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
            let E := gradientColumns (fderiv ℝ u x)
            let Ft := (A x).val * E + Matrix.of (fun i j => F (n+1 : ℝ) j x i)
            let J := operatorMatrix (fderiv ℝ Y x)
            let At := repairPushed (C z) J E Ft
            0 < J.det ∧ LinearIndependent ℝ E.col ∧ (z, At) ∈ G ∧
              At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft := by
  sorry

end ScalarConductivity

end

end OAI
end
