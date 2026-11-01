-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_source_cloud_comparison
-- name    : OAI.ContinuumCoulomb.source_cloud_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:54:30.752338+00:00
-- url     : https://prove2.me/theorems/24922012-9d89-4283-bd02-853280a0d110
-- title:
--   OAI.ContinuumCoulomb.source_cloud_comparison: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.source_cloud_comparison` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/Reduction/SourceCloudComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Reduction/SourceCloudComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb`, with `open scoped BigOperators Classical NNReal`, `open HubbardGlobal`):
--
--   ```lean
--   theorem source_cloud_comparison
--       (hflow : PublishedC4FlowInput)
--       (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
--       (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
--       ∃ (rho : ℕ) (_hrho : 0 < rho) (U F K q : ℕ), 1 ≤ q ∧
--       ∀ (r s v p k ap calC srcS pc h A B qt : ℕ) (eps c : ℚ) (d : BinaryHeisenberg),
--         q+9*r+72*s+v+p ≤ k → q+465*k+2*r+v+p+34 ≤ ap →
--       ∀ (m n : ℕ) (u : Fin (m+1) → ℚ×ℚ), n+2=m+1 →
--         (SourcePositiveProgram.output srcS d).vertices=n+2 →
--         SourceNuclearProgram.sites rho calC eps c srcS pc h k A B d=List.ofFn u →
--         (m+1:ℝ) ≤ (SourceContactProgram.size d:ℝ)^r →
--         (∀ i, ‖PlanarForcingProgram.position (u i)‖ ≤ (SourceContactProgram.size d:ℝ)^s) →
--       ∀ D : ℝ, 25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ D →
--         (∀ i j, i ≠ j → D ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖) →
--       ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
--         (∑ e, |t e|) ≤ (SourceContactProgram.size d:ℝ)^v →
--         (∀ i j, ‖((SourceNuclearProgram.amplification rho k d:ℝ):ℂ)*
--             (planarHoppingMatrix (fun a => PlanarForcingProgram.position (u a)) i j:ℂ)-
--           graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤
--             ((SourceContactProgram.size d:ℝ)^(2*r+p+7))⁻¹) →
--         (1:ℚ) ≤ (SourcePhysicalThreshold.value rho calC eps c srcS pc h k A B qt d).2-
--           (SourcePhysicalThreshold.value rho calC eps c srcS pc h k A B qt d).1 →
--       let freq := GaussianFrequency.frequency rho
--       let scale := (SourceNuclearProgram.amplification rho k d:ℝ)
--       let center := scale^2*(n+2:ℝ)*
--         (slabPotential rho (SourcePhysicalThreshold.slabHorizontal k d)
--           (SourcePhysicalThreshold.slabVertical k d) 0+((-1/2:ℝ)+freq/2))+
--         scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
--           (localizedOffsiteCoulomb freq (fun a => PlanarForcingProgram.position (u a))) left right t-
--           (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq (fun a => PlanarForcingProgram.position (u a)) i j))
--       let output := SourceUnitCoulomb.value rho calC U F K eps c srcS pc h k A B qt ap d
--       ∃ ho : output.Valid,
--         ((center-scale*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) ≤ unitGroundEnergy (output.toData ho) ∧
--         unitGroundEnergy (output.toData ho) ≤ ((center+scale*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.PlanarPosition` and `OAI.ContinuumCoulomb.GaussianFrequency.frequency` (definitions bundle `OAIQ092A000` of this split); `OAI.ContinuumCoulomb.BinaryHeisenberg`, `OAI.ContinuumCoulomb.PublishedSobolevSmoothDensity`, `OAI.ContinuumCoulomb.slabPotential`, `OAI.ContinuumCoulomb.HubbardGlobal.graphHoppingMatrix`, `OAI.ContinuumCoulomb.HubbardGlobal.hubbardFermionBottom`, `OAI.ContinuumCoulomb.SourceContactProgram.size` and `OAI.ContinuumCoulomb.SourcePositiveProgram.Registers` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.localizedCoulombProfile` and `OAI.ContinuumCoulomb.PlanarForcingProgram.position` (definitions bundle `OAIQ092A004` of this split); `OAI.ContinuumCoulomb.PublishedVerticalOscillatorGap` (definitions bundle `OAIQ092A005` of this split); `OAI.ContinuumCoulomb.SourceNuclearProgram.amplification`, `OAI.ContinuumCoulomb.SourcePhysicalThreshold.slabHorizontal` and `OAI.ContinuumCoulomb.SourcePhysicalThreshold.slabVertical` (definitions bundle `OAIQ092A007` of this split); `OAI.ContinuumCoulomb.PublishedC4FlowInput`, `OAI.ContinuumCoulomb.PlanarSobolev.ManufacturedPlanarGroundGap` and `OAI.ContinuumCoulomb.SourcePositiveProgram.output` (definitions bundle `OAIQ092A008` of this split); `OAI.ContinuumCoulomb.localizedOffsiteCoulomb` and `OAI.ContinuumCoulomb.planarHoppingMatrix` (definitions bundle `OAIQ092A009` of this split); `OAI.ContinuumCoulomb.SourceNuclearProgram.sites`, `OAI.ContinuumCoulomb.SourcePhysicalThreshold.value` and `OAI.ContinuumCoulomb.SourceUnitCoulomb.value` (definitions bundle `OAIQ092A010` of this split); `OAI.ContinuumCoulomb.Position`, `OAI.ContinuumCoulomb.UnitCoulomb`, `OAI.ContinuumCoulomb.unitGroundEnergy`, `OAI.ContinuumCoulomb.UnitCoulomb.Valid` and `OAI.ContinuumCoulomb.UnitCoulomb.toData` (the published bundle `Def_ContinuumCoulombHardness`).
--
--   **Used by.** The proof of `OAI.ContinuumCoulomb.exists_source_unit_reduction_with_planar_gap` of this split imports it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Reduction/SourceCloudComparison.lean (declaration OAI.ContinuumCoulomb.source_cloud_comparison)

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
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
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb
open HubbardGlobal

theorem source_cloud_comparison
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
    ∃ (rho : ℕ) (_hrho : 0 < rho) (U F K q : ℕ), 1 ≤ q ∧
    ∀ (r s v p k ap calC srcS pc h A B qt : ℕ) (eps c : ℚ) (d : BinaryHeisenberg),
      q+9*r+72*s+v+p ≤ k → q+465*k+2*r+v+p+34 ≤ ap →
    ∀ (m n : ℕ) (u : Fin (m+1) → ℚ×ℚ), n+2=m+1 →
      (SourcePositiveProgram.output srcS d).vertices=n+2 →
      SourceNuclearProgram.sites rho calC eps c srcS pc h k A B d=List.ofFn u →
      (m+1:ℝ) ≤ (SourceContactProgram.size d:ℝ)^r →
      (∀ i, ‖PlanarForcingProgram.position (u i)‖ ≤ (SourceContactProgram.size d:ℝ)^s) →
    ∀ D : ℝ, 25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ D →
      (∀ i j, i ≠ j → D ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖) →
    ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (∑ e, |t e|) ≤ (SourceContactProgram.size d:ℝ)^v →
      (∀ i j, ‖((SourceNuclearProgram.amplification rho k d:ℝ):ℂ)*
          (planarHoppingMatrix (fun a => PlanarForcingProgram.position (u a)) i j:ℂ)-
        graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤
          ((SourceContactProgram.size d:ℝ)^(2*r+p+7))⁻¹) →
      (1:ℚ) ≤ (SourcePhysicalThreshold.value rho calC eps c srcS pc h k A B qt d).2-
        (SourcePhysicalThreshold.value rho calC eps c srcS pc h k A B qt d).1 →
    let freq := GaussianFrequency.frequency rho
    let scale := (SourceNuclearProgram.amplification rho k d:ℝ)
    let center := scale^2*(n+2:ℝ)*
      (slabPotential rho (SourcePhysicalThreshold.slabHorizontal k d)
        (SourcePhysicalThreshold.slabVertical k d) 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq (fun a => PlanarForcingProgram.position (u a))) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq (fun a => PlanarForcingProgram.position (u a)) i j))
    let output := SourceUnitCoulomb.value rho calC U F K eps c srcS pc h k A B qt ap d
    ∃ ho : output.Valid,
      ((center-scale*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) ≤ unitGroundEnergy (output.toData ho) ∧
      unitGroundEnergy (output.toData ho) ≤ ((center+scale*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) := by
  sorry

end ContinuumCoulomb

end

end OAI
end
