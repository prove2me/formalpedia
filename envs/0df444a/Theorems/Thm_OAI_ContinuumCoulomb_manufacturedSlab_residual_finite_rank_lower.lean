-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_manufacturedSlab_residual_finite_rank_lower
-- name    : OAI.ContinuumCoulomb.manufacturedSlab_residual_finite_rank_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:52:49.543146+00:00
-- url     : https://prove2.me/theorems/c29e2947-f133-4308-8a5b-e3ad94178615
-- title:
--   OAI.ContinuumCoulomb.manufacturedSlab_residual_finite_rank_lower: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.manufacturedSlab_residual_finite_rank_lower` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedResidualGap.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedResidualGap.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb`):
--
--   ```lean
--   theorem manufacturedSlab_residual_finite_rank_lower
--       (hdensity : PublishedSobolevSmoothDensity) {rho H S freq δ D R γ ε : ℝ}
--       (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
--       (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
--       (hγ : 0 < γ) (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
--       (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
--       (hδ : 0 ≤ δ) (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
--         localizedCounterterm freq u j/scale ≤ δ)
--       (hε : 0 ≤ ε) (herr : 4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j) ≤ ε^2)
--       (hgap : ∀ v : Coulomb.H1Vector 1,
--         (∀ s i, inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
--           (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) = 0) →
--         ((-1/2:ℝ)+freq/2+γ/2)*Coulomb.mass v ≤
--           boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
--             (oneElectronCoordinates x)) v)
--       (v : Coulomb.H1Vector 1) :
--       ((-1/2:ℝ)+freq/2+γ/4)*Coulomb.mass v-
--         (γ/4+ε+ε^2/(γ/4))*graphOrbitalMass
--           (fun i => oneElectronOrbitalLp (correctedLocalizedMode freq u i)
--             (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v) ≤
--         boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
--           (oneElectronCoordinates x)) v
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.PlanarPosition` (definitions bundle `OAIQ092A000` of this split); `OAI.ContinuumCoulomb.PublishedSobolevSmoothDensity` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.boundedPotentialForm` (definitions bundle `OAIQ092A002` of this split); `OAI.ContinuumCoulomb.oneElectronCoordinates` and `OAI.ContinuumCoulomb.oneElectronOrbitalLp` (definitions bundle `OAIQ092A003` of this split); `OAI.ContinuumCoulomb.correctedLocalizedMode`, `OAI.ContinuumCoulomb.graphOrbitalMass`, `OAI.ContinuumCoulomb.h1Coordinates` and `OAI.ContinuumCoulomb.localizedOverlapBound` (definitions bundle `OAIQ092A007` of this split); `OAI.ContinuumCoulomb.correctedLocalizedMode_memLp`, `OAI.ContinuumCoulomb.localizedCounterterm` and `OAI.ContinuumCoulomb.manufacturedSlabPotential` (definitions bundle `OAIQ092A009` of this split); `OAI.ContinuumCoulomb.manufacturedOrbitalSquaredError` (definitions bundle `OAIQ092A010` of this split); `OAI.ContinuumCoulomb.Configuration`, `OAI.ContinuumCoulomb.Position`, `OAI.ContinuumCoulomb.SpinConfiguration`, `OAI.Coulomb.H1Vector` and `OAI.Coulomb.mass` (the published bundle `Def_ContinuumCoulombHardness`).
--
--   **Used by.** The proofs of `OAI_ContinuumCoulomb_manufacturedSlab_uniform_precise_manyElectron_lower`, `OAI_ContinuumCoulomb_manufacturedSlab_uniform_tensorComplement_coercivity` and `OAI.ContinuumCoulomb.manufacturedSlab_uniform_tensorComplement_gap` of this split import it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedResidualGap.lean (declaration OAI.ContinuumCoulomb.manufacturedSlab_residual_finite_rank_lower)

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ContinuumCoulomb

theorem manufacturedSlab_residual_finite_rank_lower
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq δ D R γ ε : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hfreq : 0 < freq)
    (hrelation : freq^2 = 4*Real.pi*rho) (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (hγ : 0 < γ) (scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖) (hs : m*localizedOverlapBound D ≤ 1/2)
    (hδ : 0 ≤ δ) (hcoeff : ∀ j, 0 ≤ localizedCounterterm freq u j/scale ∧
      localizedCounterterm freq u j/scale ≤ δ)
    (hε : 0 ≤ ε) (herr : 4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D R u j) ≤ ε^2)
    (hgap : ∀ v : Coulomb.H1Vector 1,
      (∀ s i, inner ℂ (oneElectronOrbitalLp (correctedLocalizedMode freq u i)
        (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v (Sum.inl s)) = 0) →
      ((-1/2:ℝ)+freq/2+γ/2)*Coulomb.mass v ≤
        boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
          (oneElectronCoordinates x)) v)
    (v : Coulomb.H1Vector 1) :
    ((-1/2:ℝ)+freq/2+γ/4)*Coulomb.mass v-
      (γ/4+ε+ε^2/(γ/4))*graphOrbitalMass
        (fun i => oneElectronOrbitalLp (correctedLocalizedMode freq u i)
          (correctedLocalizedMode_memLp hfreq u i)) (h1Coordinates v) ≤
      boundedPotentialForm (fun x => manufacturedSlabPotential rho H S freq scale u
        (oneElectronCoordinates x)) v := by
  sorry

end ContinuumCoulomb

end

end OAI
end
