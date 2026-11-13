-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_all_orders_primitive_normal_geometry
-- name    : OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.all_orders_primitive_normal_geometry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:48:02.231169+00:00
-- url     : https://prove2.me/theorems/9358f97c-b6c4-49ee-b077-682028b91f5b
-- title:
--   OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.all_orders_primitive_normal_geometry: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.all_orders_primitive_normal_geometry` of [lean/OAI/Geometry/SurfaceImmersion/Correction/UniformPrimitiveMeanRealization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/UniformPrimitiveMeanRealization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector`, `open WeightedEstimates NormalFrame`):
--
--   ```lean
--   theorem all_orders_primitive_normal_geometry {S : TopologicalSpace.Opens JetPolynomial.Base}
--       {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
--       (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
--       (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
--       ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ n : ℕ, ∃ loss : ℕ,
--         ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
--         ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
--           (hGQ : MapsTo (lowJet G) S Q),
--         ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
--         WeightedBound S s ((2*n+2)+2) B (lowJet G) → D*z/s^loss < ε →
--         ∀ U : ℕ → Family S Euclidean,
--           (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
--           (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
--           U 0 = (l.geometry G hG (fun _ hp => hQO (hGQ hp))).initial →
--         ∀ p ∈ S,
--           let H := primitiveNormalTriple (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
--             U ℓ (n+1) z) p
--           gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.coordinateVector`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.JetVelocityCoordinates.Euclidean`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet` and `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realNormalPart` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.val` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.VelocityFrame.NormalTriple` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.JetVelocityCoordinates.toEuclidean` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.primitiveNormalTriple` (definitions bundle `OAIQ249SI009` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.geometry` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.finiteAnsatz`, `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.Represents`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.initial` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.coefficientExpressions` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/UniformPrimitiveMeanRealization.lean (declaration OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.all_orders_primitive_normal_geometry)

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
import Mathlib.Topology.UniformSpace.HeineCantor
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
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector
open WeightedEstimates NormalFrame
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem all_orders_primitive_normal_geometry {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hx : ℓ (coordinateVector 0) = 1) (hy : ℓ (coordinateVector 1) = 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ n : ℕ, ∃ loss : ℕ,
      ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGQ : MapsTo (lowJet G) S Q),
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      WeightedBound S s ((2*n+2)+2) B (lowJet G) → D*z/s^loss < ε →
      ∀ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) →
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) →
        U 0 = (l.geometry G hG (fun _ hp => hQO (hGQ hp))).initial →
      ∀ p ∈ S,
        let H := primitiveNormalTriple (finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
          U ℓ (n+1) z) p
        gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  sorry

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end
