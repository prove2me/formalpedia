-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_PhaseGeometry_CompactPhaseFamily_uniform_polynomial_solvers_all_profiles
-- name    : OAI.ClosedSurfaceR4.PhaseGeometry.CompactPhaseFamily.uniform_polynomial_solvers_all_profiles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:52:04.727737+00:00
-- url     : https://prove2.me/theorems/23d84cd9-171b-48ed-96bf-2c09e887f3f2
-- title:
--   OAI.ClosedSurfaceR4.PhaseGeometry.CompactPhaseFamily.uniform_polynomial_solvers_all_profiles: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.PhaseGeometry.CompactPhaseFamily.uniform_polynomial_solvers_all_profiles` of [lean/OAI/Geometry/SurfaceImmersion/Correction/UniformPolynomialCompactFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/UniformPolynomialCompactFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.PhaseGeometry`, with `open Set TopologicalSpace`, `open scoped ContDiff NNReal BigOperators`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates`):
--
--   ```lean
--   theorem CompactPhaseFamily.uniform_polynomial_solvers_all_profiles {n : ℕ}
--       (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
--       {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
--       {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
--       {K : Compacts SmallModes.Base} (a : CompactPhaseFamily F φ K)
--       {U : Set JetPolynomial.Base} (hU : IsOpen U) (KU : Compacts JetPolynomial.Base)
--       (hUK : U ⊆ KU) (hKU : (jetSupport K : Set JetPolynomial.Base) ⊆ U) :
--       ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℕ → ℝ, (∀ m, 0 ≤ R m) →
--       ∃ C D J I : a.centers → ℕ → ℝ,
--         (∀ i m, 0 ≤ C i m) ∧ (∀ i m, 0 ≤ D i m) ∧
--         (∀ i m, 1 ≤ J i m) ∧ (∀ i m, 1 ≤ I i m) ∧
--         ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G) (B : ℝ),
--         0 ≤ B → B < ρ → WeightedBound univ 1 2 B
--           ((G ∘ planeCoordinateIsometry.symm)-(F ∘ planeCoordinateIsometry.symm)) →
--         ∀ (τ ε : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         0 ≤ ε → ε ≤ 1 →
--         (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
--           (G ∘ planeCoordinateIsometry.symm)) →
--         ∃ c : (i : a.centers) → PolynomialSolveData P ε G hG φ (a.support i) τ s,
--           (∀ i, (c i).C = C i) ∧ (∀ i, (c i).D = D i) ∧ (∀ i, (c i).J = J i) ∧
--           ∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c i).e.target,
--             ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ I i m
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.jetSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.CompactPhaseFamily` and `OAI.ClosedSurfaceR4.PhaseGeometry.CompactPhaseFamily.support` (definitions bundle `OAIQ249SI007` of this split).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles` and `OAI_ClosedSurfaceR4_PhaseGeometry_uniform_polynomial_nearby_cancellation_all_profiles` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/UniformPolynomialCompactFamily.lean (declaration OAI.ClosedSurfaceR4.PhaseGeometry.CompactPhaseFamily.uniform_polynomial_solvers_all_profiles)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem CompactPhaseFamily.uniform_polynomial_solvers_all_profiles {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Compacts SmallModes.Base} (a : CompactPhaseFamily F φ K)
    {U : Set JetPolynomial.Base} (hU : IsOpen U) (KU : Compacts JetPolynomial.Base)
    (hUK : U ⊆ KU) (hKU : (jetSupport K : Set JetPolynomial.Base) ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℕ → ℝ, (∀ m, 0 ≤ R m) →
    ∃ C D J I : a.centers → ℕ → ℝ,
      (∀ i m, 0 ≤ C i m) ∧ (∀ i m, 0 ≤ D i m) ∧
      (∀ i m, 1 ≤ J i m) ∧ (∀ i m, 1 ≤ I i m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G) (B : ℝ),
      0 ≤ B → B < ρ → WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm)-(F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ ε : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∃ c : (i : a.centers) → PolynomialSolveData P ε G hG φ (a.support i) τ s,
        (∀ i, (c i).C = C i) ∧ (∀ i, (c i).D = D i) ∧ (∀ i, (c i).J = J i) ∧
        ∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c i).e.target,
          ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ I i m := by
  sorry

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end
