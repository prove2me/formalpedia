-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_exists_source_target_parameters
-- name    : OAI.ContinuumCoulomb.exists_source_target_parameters
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:50:21.03874+00:00
-- url     : https://prove2.me/theorems/10e85f21-f6d1-45cb-9863-82913f920d28
-- title:
--   OAI.ContinuumCoulomb.exists_source_target_parameters: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.exists_source_target_parameters` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/Reduction/SourceTargetHubbard.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Reduction/SourceTargetHubbard.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb`, with `open scoped BigOperators`, `open SourcePositiveProgram SourceMetadataProgram ContactMediator HubbardGlobal`):
--
--   ```lean
--   theorem exists_source_target_parameters (rho : ℕ) (hrho : 0 < rho) (s g : ℕ) :
--       ∃ A B v q : ℕ, 0 < A ∧ 0 < B ∧ 1 ≤ v ∧ 1 ≤ q ∧
--         ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s →
--         ∀ (m k : ℕ) (hm : (output s d).vertices=m+1), q ≤ k →
--         ∀ (D : ℝ) (u : Fin (m+1) → PlanarPosition),
--         25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ D →
--         (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
--         let F := indexedGraph s d hd hm
--         let N : ℝ := SourceContactProgram.size d
--         let τ := (N^(30*B))⁻¹
--         let freq := GaussianFrequency.frequency rho
--         let t := fun e => -coulombHoppingTarget freq τ (F.weight e) ‖u (F.left e)-u (F.right e)‖
--         (∀ e, (N^(30*A))⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ N^(30*A)) ∧
--         (∑ e, |t e|) ≤ N^v ∧
--         |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
--             F.left F.right t-
--           graphSourceBottom m F.left F.right (fun e => τ^2*(F.weight e:ℝ))| ≤ (N^g)⁻¹*τ^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.PlanarPosition` and `OAI.ContinuumCoulomb.GaussianFrequency.frequency` (definitions bundle `OAIQ092A000` of this split); `OAI.ContinuumCoulomb.BinaryHeisenberg`, `OAI.ContinuumCoulomb.BinaryHeisenberg.PolynomialPromise`, `OAI.ContinuumCoulomb.BinaryHeisenberg.Valid`, `OAI.ContinuumCoulomb.HubbardGlobal.graphSourceBottom`, `OAI.ContinuumCoulomb.HubbardGlobal.hubbardFermionBottom`, `OAI.ContinuumCoulomb.MediatorIteration.Bonds`, `OAI.ContinuumCoulomb.SourceContactProgram.size` and `OAI.ContinuumCoulomb.SourcePositiveProgram.Registers` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.coulombHoppingTarget` and `OAI.ContinuumCoulomb.localizedCoulombProfile` (definitions bundle `OAIQ092A004` of this split); `OAI.ContinuumCoulomb.SourcePositiveProgram.graphEdgeCount` (definitions bundle `OAIQ092A007` of this split); `OAI.ContinuumCoulomb.SourcePositiveProgram.output` (definitions bundle `OAIQ092A008` of this split); `OAI.ContinuumCoulomb.localizedOffsiteCoulomb` (definitions bundle `OAIQ092A009` of this split); `OAI.ContinuumCoulomb.SourcePositiveProgram.indexedGraph` (definitions bundle `OAIQ092A010` of this split).
--
--   **Used by.** The proof of `OAI.ContinuumCoulomb.exists_source_unit_reduction_with_planar_gap` of this split imports it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Reduction/SourceTargetHubbard.lean (declaration OAI.ContinuumCoulomb.exists_source_target_parameters)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Round
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
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.ODE.ExistUnique
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAIQ092A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open SourcePositiveProgram SourceMetadataProgram ContactMediator HubbardGlobal

theorem exists_source_target_parameters (rho : ℕ) (hrho : 0 < rho) (s g : ℕ) :
    ∃ A B v q : ℕ, 0 < A ∧ 0 < B ∧ 1 ≤ v ∧ 1 ≤ q ∧
      ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s →
      ∀ (m k : ℕ) (hm : (output s d).vertices=m+1), q ≤ k →
      ∀ (D : ℝ) (u : Fin (m+1) → PlanarPosition),
      25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ D →
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      let F := indexedGraph s d hd hm
      let N : ℝ := SourceContactProgram.size d
      let τ := (N^(30*B))⁻¹
      let freq := GaussianFrequency.frequency rho
      let t := fun e => -coulombHoppingTarget freq τ (F.weight e) ‖u (F.left e)-u (F.right e)‖
      (∀ e, (N^(30*A))⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ N^(30*A)) ∧
      (∑ e, |t e|) ≤ N^v ∧
      |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
          F.left F.right t-
        graphSourceBottom m F.left F.right (fun e => τ^2*(F.weight e:ℝ))| ≤ (N^g)⁻¹*τ^2 := by
  sorry

end ContinuumCoulomb

end

end OAI
end
