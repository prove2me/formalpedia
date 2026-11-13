-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_input_polynomial_small_increment_fixed_phase
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:04.977211+00:00
-- url     : https://prove2.me/theorems/b315e180-c035-43f8-a447-4876b0971544
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase` of [lean/OAI/Geometry/SurfaceImmersion/Correction/InputPolynomialSmallIncrement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/InputPolynomialSmallIncrement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates`):
--
--   ```lean
--   theorem input_polynomial_small_increment_fixed_phase
--       {n : A.centers → ℕ} {nq : ℕ}
--       (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
--       (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
--       (Q : A.centers → Fin 3 → Fin nq → Expression)
--       (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
--       (hquad : A.PolynomialQuadraticRepresentation Pol Q)
--       (hlin : A.PolynomialLinearRepresentation Pol Q)
--       (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
--       (φ : A.centers × Fin 3 → M → ℝ)
--       (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
--       (hImm : ∀ k l x, x ∈ (modeSupport
--         (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
--           (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
--         Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
--       (hgood : ∀ k l x, x ∈ (modeSupport
--         (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
--           (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
--         PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
--           (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
--             φ k l)) x))
--       (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
--       (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
--       (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ω i)
--       (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
--       : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
--         ∀ (p : ∀ i, Fin 3 → ChartedMeanProfile (Q i)) {ρ R : ℝ} (hρ : 0 < ρ),
--         ∀ (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
--         (D : ℕ → ℝ) (_hD : ∀ m, 0 ≤ D m)
--       (C E : ℕ → ℝ) (_hC : ∀ m, 0 ≤ C m) (_hE : ∀ m, 0 ≤ E m) (q : ℕ),
--       ∃ B T : ℕ → ℝ,
--         (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
--         ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
--           0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
--         ∀ {ε τ : ℝ} {s : ℝ≥0}
--         (d : ∀ i, ChartedMeanFamilyData (Q i) ε τ s (r i) ρ R (reference i)),
--         (∀ i, (d i).Fits (p i)) → (∀ a : A.centers × Fin 3, A.freeGlobalPhase d a.1 a.2 = φ a) →
--         (∀ i, (d i).G = A.jetChartMap i G) →
--         0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
--         0 ≤ ε → ε ≤ 1 → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
--         τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (Q i)))
--           (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η →
--         (∀ m, A.ShiftedBound 2 m s (D m) G) →
--         (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
--           (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
--         ∀ δ : ℝ, 0 < δ → δ ≤ τ → ∀ u H : ∀ x : M, CovariantTwoTensor x,
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--           (fun x => TotalSpace.mk' TensorFiber x (u x)) →
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--           (fun x => TotalSpace.mk' TensorFiber x (H x)) →
--         (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
--         (∀ m, A.TensorWeightedBound s m (C m) u) →
--         (∀ m, A.TensorWeightedBound τ m (E m*δ^2*η^(q+1))
--           (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)) →
--         ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
--           (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
--           (∀ m, A.TensorWeightedBound τ m (T m*(δ*η^(q+1)+δ^3/τ))
--             (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteMean.InTrialBall`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.QuadraticLabel` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.phaseDerivative`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialMetric` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.freeGlobalPhase`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanProfile` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData.Fits` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialLinearRepresentation` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialQuadraticRepresentation` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData.quadraticMean` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.globalQuadraticPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.quadraticOverlapCompact` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/InputPolynomialSmallIncrement.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_small_increment_fixed_phase)

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
import Definitions.Def_OAIQ249SI012

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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasFiberSpace
local instance polynomialSmallAtlasDualAdd_r36f15a_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmallAtlasFiberNormed
local instance polynomialSmallAtlasSectionNormed_r36f15a_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSmallAtlasSectionSpace_r36f15a_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem input_polynomial_small_increment_fixed_phase
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (Q : A.centers → Fin 3 → Fin nq → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol Q)
    (hlin : A.PolynomialLinearRepresentation Pol Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : A.centers × Fin 3 → M → ℝ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hImm : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          φ k l)) x))
    (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
    (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ω i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ∀ i, Fin 3 → ChartedMeanProfile (Q i)) {ρ R : ℝ} (hρ : 0 < ρ),
      ∀ (r : A.centers → ℝ) (reference : A.centers → SmallModes.Base → Tensor)
      (D : ℕ → ℝ) (_hD : ∀ m, 0 ≤ D m)
    (C E : ℕ → ℝ) (_hC : ∀ m, 0 ≤ C m) (_hE : ∀ m, 0 ≤ E m) (q : ℕ),
    ∃ B T : ℕ → ℝ,
      (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ {ε τ : ℝ} {s : ℝ≥0}
      (d : ∀ i, ChartedMeanFamilyData (Q i) ε τ s (r i) ρ R (reference i)),
      (∀ i, (d i).Fits (p i)) → (∀ a : A.centers × Fin 3, A.freeGlobalPhase d a.1 a.2 = φ a) →
      (∀ i, (d i).G = A.jetChartMap i G) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (Q i)))
        (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η →
      (∀ m, A.ShiftedBound 2 m s (D m) G) →
      (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ τ → ∀ u H : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ m, A.TensorWeightedBound s m (C m) u) →
      (∀ m, A.TensorWeightedBound τ m (E m*δ^2*η^(q+1))
        (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)) →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*η^(q+1)+δ^3/τ))
          (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
