-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_manufactured_grid_witness
-- name    : OAI.ContinuumCoulomb.manufactured_grid_witness
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:17:17.217195+00:00
-- url     : https://prove2.me/theorems/949b83bf-bfc6-4688-bf4c-2ed7cc50b71a
-- title:
--   OAI.ContinuumCoulomb.manufactured_grid_witness: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.manufactured_grid_witness` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedGridWitness.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedGridWitness.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb`, with `open MeasureTheory`, `open scoped NNReal`):
--
--   ```lean
--   theorem manufactured_grid_witness (hp : PublishedC4FlowInput) :
--       ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ D : ℝ, 1 ≤ D ∧
--       ∀ freq : ℝ, 0 < freq → ∃ E : ℝ, 1 ≤ E ∧
--       ∀ R scale S H : ℝ, 2 ≤ R → 0 < scale → R^5 ≤ S → S ≤ 2*R^5 → 0 ≤ H →
--       ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ R^14 →
--       (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
--       (∀ i, localizedCounterterm freq u i ≤ scale) →
--       tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
--       ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
--       (⋃ i, positionCube (gaussCellCenter (1/R^10) (index i)) (1/R^10)) = slabDomain H S →
--       ∃ G : Position → ℝ → Position,
--         IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
--         Function.Bijective (fun x => G x 1) ∧
--         LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
--         (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
--         (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
--         ContDiff ℝ 4 (fun x => G x 1) ∧
--         (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) ∧
--         let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho (1/R^10) y-
--           (slabPotential rho H S y+manufacturedWellField freq scale S u y)
--         (∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
--           Integrable (fun x => |F (Coulomb.position x i)| *‖w.value s x‖^2) ∧
--           (∫ x, |F (Coulomb.position x i)| *‖w.value s x‖^2) ≤
--             (D/R^20)*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2)) ∧
--         (∀ v w : PlanarPosition,
--           Integrable (fun y => F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y) ∧
--           |∫ y, F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y| ≤
--             E*((m:ℝ)+1)/R^32)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.PlanarPosition` and `OAI.ContinuumCoulomb.continuumLocalizedMode` (definitions bundle `OAIQ092A000` of this split); `OAI.ContinuumCoulomb.IsUnitTimeFlow`, `OAI.ContinuumCoulomb.slabDomain` and `OAI.ContinuumCoulomb.slabPotential` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.positionCube` (definitions bundle `OAIQ092A002` of this split); `OAI.ContinuumCoulomb.gaussCellCenter` (definitions bundle `OAIQ092A003` of this split); `OAI.ContinuumCoulomb.gridNuclearPotential` (definitions bundle `OAIQ092A007` of this split); `OAI.ContinuumCoulomb.PublishedC4FlowInput` (definitions bundle `OAIQ092A008` of this split); `OAI.ContinuumCoulomb.localizedCounterterm`, `OAI.ContinuumCoulomb.manufacturedCharge`, `OAI.ContinuumCoulomb.manufacturedWellField` and `OAI.ContinuumCoulomb.moserVelocity` (definitions bundle `OAIQ092A009` of this split); `OAI.ContinuumCoulomb.Position`, `OAI.ContinuumCoulomb.SpinConfiguration`, `OAI.Coulomb.Configuration`, `OAI.Coulomb.H1Vector` and `OAI.Coulomb.position` (the published bundle `Def_ContinuumCoulombHardness`).
--
--   **Used by.** The proofs of `OAI_ContinuumCoulomb_manufactured_grid_parameters` and `OAI.ContinuumCoulomb.manufactured_polynomial_comparison` of this split import it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedGridWitness.lean (declaration OAI.ContinuumCoulomb.manufactured_grid_witness)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.MeasureTheory.Function.Jacobian
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
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
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
open scoped NNReal
namespace ContinuumCoulomb

theorem manufactured_grid_witness (hp : PublishedC4FlowInput) :
    ∃ rho : ℕ, 0 < rho ∧ ∃ L K : ℝ≥0, 0 < L ∧ 0 < K ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ freq : ℝ, 0 < freq → ∃ E : ℝ, 1 ≤ E ∧
    ∀ R scale S H : ℝ, 2 ≤ R → 0 < scale → R^5 ≤ S → S ≤ 2*R^5 → 0 ≤ H →
    ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ R^14 →
    (∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖) →
    (∀ i, localizedCounterterm freq u i ≤ scale) →
    tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
    ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
    (⋃ i, positionCube (gaussCellCenter (1/R^10) (index i)) (1/R^10)) = slabDomain H S →
    ∃ G : Position → ℝ → Position,
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G ∧
      Function.Bijective (fun x => G x 1) ∧
      LipschitzWith L (fun x => G x 1) ∧ AntilipschitzWith K (fun x => G x 1) ∧
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) ∧
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ (rho:ℝ)/2) ∧
      ContDiff ℝ 4 (fun x => G x 1) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k (fun y => G y 1) x‖ ≤ L) ∧
      let F : Position → ℝ := fun y => gridNuclearPotential index (fun x => G x 1) rho (1/R^10) y-
        (slabPotential rho H S y+manufacturedWellField freq scale S u y)
      (∀ (n : ℕ) (w : Coulomb.H1Vector n) (s : SpinConfiguration n) (i : Fin n),
        Integrable (fun x => |F (Coulomb.position x i)| *‖w.value s x‖^2) ∧
        (∫ x, |F (Coulomb.position x i)| *‖w.value s x‖^2) ≤
          (D/R^20)*((∫ x, ‖w.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖w.gradient s (i,k) x‖^2)) ∧
      (∀ v w : PlanarPosition,
        Integrable (fun y => F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y) ∧
        |∫ y, F y*continuumLocalizedMode freq v y*continuumLocalizedMode freq w y| ≤
          E*((m:ℝ)+1)/R^32) := by
  sorry

end ContinuumCoulomb

end

end OAI
end
