-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_input_cancellation_all_profiles
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:01.365248+00:00
-- url     : https://prove2.me/theorems/f37f51ef-4dcd-4ef4-80cc-1e17568ce857
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialInputCancellation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialInputCancellation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates`):
--
--   ```lean
--   theorem atlas_polynomial_input_cancellation_all_profiles
--       {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
--       {n : A.centers → ℕ} {nq : ℕ}
--       (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
--       (Q : A.centers → Fin 3 → Fin nq → Expression)
--       (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
--       (hrepr : A.PolynomialLinearRepresentation Pol Q)
--       (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
--       (φ : (i : A.centers) → ι i → JetPolynomial.Base → ℝ)
--       (hφ : ∀ i j, ContDiff ℝ ∞ (φ i j))
--       (K : (i : A.centers) → ι i → TopologicalSpace.Compacts JetPolynomial.Base)
--       (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
--         (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
--       (hImm : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
--         Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) p))
--       (hgood : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
--         PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) p)
--           (phaseDerivative (coordinatePhase (φ i j)) p))
--       (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
--       (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
--       (hUK : ∀ i, U i ⊆ KU i) (hKU : ∀ i j, (K i j : Set JetPolynomial.Base) ⊆ U i)
--       : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) → ∀ q : ℕ,
--       ∃ C D : (i : A.centers) → ι i → ℕ → ℝ,
--         (∀ i j m, 0 ≤ C i j m) ∧ (∀ i j m, 0 ≤ D i j m) ∧
--         ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
--           0 ≤ B → B < ρ → A.WeightedBound 1 2 B (G-F) →
--         ∀ (τ ε η : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--           0 ≤ ε → ε ≤ 1 → 0 ≤ η → η ≤ 1 →
--           (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
--           (∀ m, A.ShiftedBound 2 m s (P m) G) →
--         ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)),
--         ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ W ∧
--           (∀ m, A.WeightedBound τ m
--             (∑ i : A.centers, ∑ j, C i j m * supportedWeightedSeminorm (modeSupport (K i j))
--               s (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)) W) ∧
--           (∀ m, A.TensorWeightedBound τ m
--             (η^(q+1) * ∑ i : A.centers, ∑ j, D i j m *
--               supportedWeightedSeminorm (modeSupport (K i j)) s
--                 (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j))
--             (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
--               A.atlasPolynomialVariation Pol ε G (spaceCoordinates.symm ∘ W) +
--               A.tensorPlaneRestore (fun i x => ∑ j,
--                 QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.JetPolynomial.supportedWeightedSeminorm`, `OAI.ClosedSurfaceR4.PhaseMean.ComplexTensor`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.phaseDerivative`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.QuadraticMean.displacement`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.inputOrder` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearMetricTensor` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputPhasePolynomialDualAdd` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialLinearRepresentation` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialVariation` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_input_global_polynomial_quadratic_cancellation_all_profiles` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_free_correction_fixed_phase` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialInputCancellation.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles)

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
import Definitions.Def_OAIQ249SI010

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputPhasePolynomialDualAdd
local instance inputPhasePolynomialFiberNormed_r7831ad_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance inputPhasePolynomialFiberSpace_r7831ad_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance inputPhasePolynomialDualSmul_r7831ad_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance inputPhasePolynomialSectionNormed_r7831ad_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputPhasePolynomialSectionSpace_r7831ad_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlas_polynomial_input_cancellation_all_profiles
    {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hrepr : A.PolynomialLinearRepresentation Pol Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : (i : A.centers) → ι i → JetPolynomial.Base → ℝ)
    (hφ : ∀ i j, ContDiff ℝ ∞ (φ i j))
    (K : (i : A.centers) → ι i → TopologicalSpace.Compacts JetPolynomial.Base)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (hImm : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) p))
    (hgood : ∀ i j p, p ∈ (modeSupport (K i j) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) p)
        (phaseDerivative (coordinatePhase (φ i j)) p))
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base)
    (hUK : ∀ i, U i ⊆ KU i) (hKU : ∀ i j, (K i j : Set JetPolynomial.Base) ⊆ U i)
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) → ∀ q : ℕ,
    ∃ C D : (i : A.centers) → ι i → ℕ → ℝ,
      (∀ i j m, 0 ≤ C i j m) ∧ (∀ i j m, 0 ≤ D i j m) ∧
      ∀ (G : M → Space) (_hG : ContMDiff planeModel spaceModel ∞ G) (B : ℝ),
        0 ≤ B → B < ρ → A.WeightedBound 1 2 B (G-F) →
      ∀ (τ ε η : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
        0 ≤ ε → ε ≤ 1 → 0 ≤ η → η ≤ 1 →
        (∀ i, τ/s+ε/τ^tensorLoss (Q i) ≤ η) →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ target : ∀ i j, SupportedField (F := ComplexTensor) (modeSupport (K i j)),
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ, RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m
          (∑ i : A.centers, ∑ j, C i j m * supportedWeightedSeminorm (modeSupport (K i j))
            s (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j)) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          (η^(q+1) * ∑ i : A.centers, ∑ j, D i j m *
            supportedWeightedSeminorm (modeSupport (K i j)) s
              (PolynomialSolveData.inputOrder (P := Q i) q m) (target i j))
          (linearMetricTensor G (spaceCoordinates.symm ∘ W) +
            A.atlasPolynomialVariation Pol ε G (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun i x => ∑ j,
              QuadraticMean.displacement τ (coordinatePhase (φ i j)) (target i j) x))) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
