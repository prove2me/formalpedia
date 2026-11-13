-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_profiled_polynomial_atlas_small_increment
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:24.213539+00:00
-- url     : https://prove2.me/theorems/f946fcf8-7386-4dc3-ba4b-f053eac2fb66
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment` of [lean/OAI/Geometry/SurfaceImmersion/Correction/ProfiledPolynomialSmallIncrement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/ProfiledPolynomialSmallIncrement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean`):
--
--   ```lean
--   theorem profiled_polynomial_atlas_small_increment
--       {n : A.centers → ℕ} {nq : ℕ}
--       (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
--       (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
--       (P : A.centers → Fin 3 → Fin nq → Expression)
--       (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
--       (hquad : A.PolynomialQuadraticRepresentation Pol P)
--       (hlin : A.PolynomialLinearRepresentation Pol P)
--       (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
--       {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
--       (reference : ∀ x : M, CovariantTwoTensor x)
--       (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--         (fun x => TotalSpace.mk' TensorFiber x (reference x)))
--       (p : ∀ i, Fin 3 → ChartedMeanProfile (P i))
--       (d₀ : ∀ i, ChartedMeanFamilyData (P i) 0 1 1 r₁ ρ R (A.tensorPlaneRead i reference))
--       (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
--       (hw : ∀ i j, w i j ≠ 0)
--       (hphase₀ : ∀ i j, coordinatePhase ((d₀ i).phase j) = phaseLinear (w i j • (Q i).ξ j))
--       (hImm : ∀ k l x, x ∈ (modeSupport
--         (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
--           (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
--         Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
--       (hgood : ∀ k l x, x ∈ (modeSupport
--         (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
--           (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
--         PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
--           (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
--             (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) k l)) x))
--       (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
--       (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
--       (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ω i)
--       (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
--       (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
--       (q : ℕ) :
--       ∃ r D₀ : ℝ, 0 < r ∧ 1 ≤ D₀ ∧ D₀*r ≤ r₁ ∧
--         ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
--         ∃ (ρ₀ η₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
--           (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
--         ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
--           0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
--         ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
--           (∀ m, A.ShiftedBound 2 m s (D m) G) →
--         ∀ (H : ∀ x : M, CovariantTwoTensor x),
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--           (fun x => TotalSpace.mk' TensorFiber x (H x)) →
--         (∀ x v v', H x v v' = H x v' v) →
--         (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
--         (∀ m, A.TensorWeightedBound s m (C m) H) →
--         ∀ τ δ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
--         τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (P i)))
--           (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η₀ → 0 < δ → δ ≤ τ →
--         ∀ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference),
--           (∀ i, (d i).Fits (p i)) →
--           (∀ i, (d i).phase = (d₀ i).phase) →
--           (∀ i, (d i).G = A.jetChartMap i G) →
--           (∀ i j x, x ∈ ((d i).solver j).e.source →
--             ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) →
--           (∀ i j x, x ∈ ((d i).solver j).e.source →
--             ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) →
--           (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) →
--           (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
--             (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
--         ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
--           (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
--           (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (P i)))
--               (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))))^(q+1)+δ^3/τ))
--             (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.QuadraticLabel` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.phaseDerivative`, `OAI.ClosedSurfaceR4.phaseLinear`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.planeWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialMetric` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.freeGlobalPhase`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanProfile`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.ChartedMeanFamilyData.Fits` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.chartCompact` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledPolynomialSmallDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledPolynomialSmallFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledPolynomialSmallFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialLinearRepresentation` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialQuadraticRepresentation` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.globalQuadraticPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.quadraticOverlapCompact`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorEncode` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_small_increment`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_geometry_polynomial_increment` and `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_polynomial_atlas_small_increment` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/ProfiledPolynomialSmallIncrement.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment)

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
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledPolynomialSmallFiberSpace
local instance profiledPolynomialSmallDualAdd_rb16a01_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledPolynomialSmallDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledPolynomialSmallFiberNormed
local instance profiledPolynomialSmallSectionNormed_rb16a01_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance profiledPolynomialSmallSectionSpace_rb16a01_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem profiled_polynomial_atlas_small_increment
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (P : A.centers → Fin 3 → Fin nq → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol P)
    (hlin : A.PolynomialLinearRepresentation Pol P)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i))
    (d₀ : ∀ i, ChartedMeanFamilyData (P i) 0 1 1 r₁ ρ R (A.tensorPlaneRead i reference))
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase₀ : ∀ i j, coordinatePhase ((d₀ i).phase j) = phaseLinear (w i j • (Q i).ξ j))
    (hImm : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) k l)) x))
    (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
    (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ω i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (q : ℕ) :
    ∃ r D₀ : ℝ, 0 < r ∧ 1 ≤ D₀ ∧ D₀*r ≤ r₁ ∧
      ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (ρ₀ η₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (D m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (P i)))
        (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η₀ → 0 < δ → δ ≤ τ →
      ∀ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference),
        (∀ i, (d i).Fits (p i)) →
        (∀ i, (d i).phase = (d₀ i).phase) →
        (∀ i, (d i).G = A.jetChartMap i G) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) →
        (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) →
        (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
          (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (P i)))
            (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))))^(q+1)+δ^3/τ))
          (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
