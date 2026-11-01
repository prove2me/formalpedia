-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_manufactured_polynomial_comparison
-- name    : OAI.ContinuumCoulomb.manufactured_polynomial_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:20:35.1768+00:00
-- url     : https://prove2.me/theorems/6a08831c-55a0-4277-8c35-71fc41035501
-- title:
--   OAI.ContinuumCoulomb.manufactured_polynomial_comparison: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.manufactured_polynomial_comparison` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedPolynomialComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedPolynomialComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb`, with `open MeasureTheory`, `open scoped BigOperators Classical NNReal`, `open HubbardGlobal`):
--
--   ```lean
--   theorem manufactured_polynomial_comparison
--       (hflow : PublishedC4FlowInput)
--       (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
--       (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
--       ∃ (rho : ℕ) (hrho : 0 < rho), ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧
--       let freq := GaussianFrequency.frequency rho
--       ∃ q : ℕ, 1 ≤ q ∧ ∀ r s v p k : ℕ, q+9*r+72*s+v+p ≤ k →
--       ∀ N H S D : ℝ, ∀ hN : 2 ≤ N,
--         (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
--         (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
--       ∀ (m n : ℕ) (u : Fin (m+1) → PlanarPosition), n+2=m+1 →
--         (m+1:ℝ) ≤ N^r → (∀ i, ‖u i‖ ≤ N^s) →
--         (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
--       ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
--         (∑ e, |t e|) ≤ N^v →
--         (∀ i j, ‖((((8/(rho:ℝ))*(N^k)^30)*planarHoppingMatrix u i j:ℝ):ℂ)-
--           graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ (N^(2*r+p+6))⁻¹) →
--       ∀ {ι : Type} [Fintype ι] [Nonempty ι] (index : ι → Fin 3 → ℤ)
--         (hindex : Function.Injective index),
--         (⋃ i, positionCube (gaussCellCenter (1/(N^k)^10) (index i)) (1/(N^k)^10)) = slabDomain H S →
--       let scale := (8/(rho:ℝ))*(N^k)^30
--       let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
--         scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
--           (localizedOffsiteCoulomb freq u) left right t-
--           (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j))
--       ∃ (G : Position → ℝ → Position) (hbij : Function.Bijective (fun x => G x 1)),
--         IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
--         LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
--         (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
--         (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
--         ContDiff ℝ 4 (fun x => G x 1) ∧
--         (∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ j (fun y => G y 1) x‖ ≤ L) ∧
--         (∀ i, localizedCounterterm freq u i ≤ scale) ∧
--         ((center-scale*(N^p)⁻¹:ℝ):EReal) ≤
--           formGroundEnergy (dilatedNuclei
--             (gridNuclei index hindex (fun x => G x 1) hbij.injective (manufactured_mesh_positive hN k))
--             scale (manufactured_scale_positive hrho hN k).ne') (n+2) ∧
--         formGroundEnergy (dilatedNuclei
--             (gridNuclei index hindex (fun x => G x 1) hbij.injective (manufactured_mesh_positive hN k))
--             scale (manufactured_scale_positive hrho hN k).ne') (n+2) ≤
--           ((center+scale*(N^p)⁻¹:ℝ):EReal)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.PlanarPosition` and `OAI.ContinuumCoulomb.GaussianFrequency.frequency` (definitions bundle `OAIQ092A000` of this split); `OAI.ContinuumCoulomb.IsUnitTimeFlow`, `OAI.ContinuumCoulomb.PublishedSobolevSmoothDensity`, `OAI.ContinuumCoulomb.slabDomain`, `OAI.ContinuumCoulomb.slabPotential`, `OAI.ContinuumCoulomb.HubbardGlobal.graphHoppingMatrix` and `OAI.ContinuumCoulomb.HubbardGlobal.hubbardFermionBottom` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.positionCube` (definitions bundle `OAIQ092A002` of this split); `OAI.ContinuumCoulomb.dilatedNuclei`, `OAI.ContinuumCoulomb.formGroundEnergy`, `OAI.ContinuumCoulomb.gaussCellCenter`, `OAI.ContinuumCoulomb.manufactured_mesh_positive` and `OAI.ContinuumCoulomb.manufactured_scale_positive` (definitions bundle `OAIQ092A003` of this split); `OAI.ContinuumCoulomb.localizedCoulombProfile` (definitions bundle `OAIQ092A004` of this split); `OAI.ContinuumCoulomb.PublishedVerticalOscillatorGap` (definitions bundle `OAIQ092A005` of this split); `OAI.ContinuumCoulomb.gridNuclei` (definitions bundle `OAIQ092A007` of this split); `OAI.ContinuumCoulomb.PublishedC4FlowInput` and `OAI.ContinuumCoulomb.PlanarSobolev.ManufacturedPlanarGroundGap` (definitions bundle `OAIQ092A008` of this split); `OAI.ContinuumCoulomb.localizedCounterterm`, `OAI.ContinuumCoulomb.localizedOffsiteCoulomb`, `OAI.ContinuumCoulomb.manufacturedCharge`, `OAI.ContinuumCoulomb.manufacturedWellField`, `OAI.ContinuumCoulomb.moserVelocity` and `OAI.ContinuumCoulomb.planarHoppingMatrix` (definitions bundle `OAIQ092A009` of this split); `OAI.ContinuumCoulomb.Position` (the published bundle `Def_ContinuumCoulombHardness`).
--
--   **Used by.** The proof of `OAI.ContinuumCoulomb.source_cloud_comparison` of this split imports it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedPolynomialComparison.lean (declaration OAI.ContinuumCoulomb.manufactured_polynomial_comparison)

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
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Size
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
import Definitions.Def_OAIQ092A008
import Definitions.Def_OAIQ092A009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb
open HubbardGlobal

theorem manufactured_polynomial_comparison
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity) :
    ∃ (rho : ℕ) (hrho : 0 < rho), ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧
    let freq := GaussianFrequency.frequency rho
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r s v p k : ℕ, q+9*r+72*s+v+p ≤ k →
    ∀ N H S D : ℝ, ∀ hN : 2 ≤ N,
      (N^k)^50 ≤ H → H ≤ 2*(N^k)^50 →
      (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 → 25*(k:ℝ)*Real.log N ≤ D →
    ∀ (m n : ℕ) (u : Fin (m+1) → PlanarPosition), n+2=m+1 →
      (m+1:ℝ) ≤ N^r → (∀ i, ‖u i‖ ≤ N^s) →
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
    ∀ {Edge : Type} [Fintype Edge] (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (∑ e, |t e|) ≤ N^v →
      (∀ i j, ‖((((8/(rho:ℝ))*(N^k)^30)*planarHoppingMatrix u i j:ℝ):ℂ)-
        graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ (N^(2*r+p+6))⁻¹) →
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] (index : ι → Fin 3 → ℤ)
      (hindex : Function.Injective index),
      (⋃ i, positionCube (gaussCellCenter (1/(N^k)^10) (index i)) (1/(N^k)^10)) = slabDomain H S →
    let scale := (8/(rho:ℝ))*(N^k)^30
    let center := scale^2*(n+2:ℝ)*(slabPotential rho H S 0+((-1/2:ℝ)+freq/2))+
      scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0)
        (localizedOffsiteCoulomb freq u) left right t-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j))
    ∃ (G : Position → ℝ → Position) (hbij : Function.Bijective (fun x => G x 1)),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ j (fun y => G y 1) x‖ ≤ L) ∧
      (∀ i, localizedCounterterm freq u i ≤ scale) ∧
      ((center-scale*(N^p)⁻¹:ℝ):EReal) ≤
        formGroundEnergy (dilatedNuclei
          (gridNuclei index hindex (fun x => G x 1) hbij.injective (manufactured_mesh_positive hN k))
          scale (manufactured_scale_positive hrho hN k).ne') (n+2) ∧
      formGroundEnergy (dilatedNuclei
          (gridNuclei index hindex (fun x => G x 1) hbij.injective (manufactured_mesh_positive hN k))
          scale (manufactured_scale_positive hrho hN k).ne') (n+2) ≤
        ((center+scale*(N^p)⁻¹:ℝ):EReal) := by
  sorry

end ContinuumCoulomb

end

end OAI
end
