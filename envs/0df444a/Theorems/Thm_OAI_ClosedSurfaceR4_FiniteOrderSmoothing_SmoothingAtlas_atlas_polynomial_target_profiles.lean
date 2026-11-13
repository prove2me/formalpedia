-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_target_profiles
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_target_profiles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:47.962211+00:00
-- url     : https://prove2.me/theorems/9805b41a-f10e-4c55-9444-dd92b7a97732
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_target_profiles: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_target_profiles` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialTargetProfiles.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialTargetProfiles.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology NNReal BigOperators`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`):
--
--   ```lean
--   theorem atlas_polynomial_target_profiles {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
--       (Q : A.centers → Fin 3 → Fin n → Expression)
--       (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
--       (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
--       (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
--       (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ KU i)
--       (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i)
--       (R a : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) (ha : ∀ m, 0 ≤ a m) :
--       ∃ E : A.centers → ℕ → ℝ, (∀ i m, 0 ≤ E i m) ∧
--         ∀ (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
--           (Z : ι → M → Fin 4 → ℂ) (hZ : ∀ b, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z b))
--           (s : ℝ≥0) (δ τ ε : ℝ), 0 < δ → 0 < τ → 0 < (s:ℝ) → τ ≤ s → s ≤ 1 →
--         0 ≤ ε → ε ≤ 1 → (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ 1) →
--         (∀ m, A.ShiftedBound 2 m s (R m) G) →
--         (∀ i b m, WeightedEstimates.WeightedBound univ s m (a m*(δ*τ)) (A.vectorPlaneRead i (Z b))) →
--         ∀ i m l, WeightedEstimates.WeightedBound univ s m (E i m*δ^2)
--           (A.globalPolynomialQuadraticTarget Q hQ G hG ε τ φ Z hφ hZ i l)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.PhaseMean.ComplexTensor`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.QuadraticLabel` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.globalPolynomialQuadraticTarget` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_input_global_polynomial_quadratic_cancellation_all_profiles` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_free_correction_fixed_phase` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialTargetProfiles.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_target_profiles)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology NNReal BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_polynomial_target_profiles {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : A.centers → Fin 3 → Fin n → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ KU i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U i)
    (R a : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) (ha : ∀ m, 0 ≤ a m) :
    ∃ E : A.centers → ℕ → ℝ, (∀ i m, 0 ≤ E i m) ∧
      ∀ (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
        (Z : ι → M → Fin 4 → ℂ) (hZ : ∀ b, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z b))
        (s : ℝ≥0) (δ τ ε : ℝ), 0 < δ → 0 < τ → 0 < (s:ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ 1) →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      (∀ i b m, WeightedEstimates.WeightedBound univ s m (a m*(δ*τ)) (A.vectorPlaneRead i (Z b))) →
      ∀ i m l, WeightedEstimates.WeightedBound univ s m (E i m*δ^2)
        (A.globalPolynomialQuadraticTarget Q hQ G hG ε τ φ Z hφ hZ i l) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
