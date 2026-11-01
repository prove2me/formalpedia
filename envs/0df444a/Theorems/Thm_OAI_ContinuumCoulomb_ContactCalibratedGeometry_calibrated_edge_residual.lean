-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_ContactCalibratedGeometry_calibrated_edge_residual
-- name    : OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:57:43.045096+00:00
-- url     : https://prove2.me/theorems/1ca4f4a3-ae47-4e71-85a3-a147e8e93f1d
-- title:
--   OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ContactCalibratedGeometry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ContactCalibratedGeometry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb.ContactCalibratedGeometry`, with `open ContactMediator MediatorIteration`, `open scoped BigOperators`):
--
--   ```lean
--   theorem calibrated_edge_residual (d : SquareLatticeHeisenberg) (W G P : ℕ)
--       {q : ℚ} (hq : 0 < q) (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
--       (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
--       {freq D scale τ ε : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
--       (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2)
--       (hDq : D ≤ (9 / 10 : ℝ) * q) (hscale : 0 ≤ scale) (hτ : 0 ≤ τ)
--       (K : GlobalEdge d → ℝ) (hK : ∀ a, 0 ≤ K a)
--       (hres : ∀ a, |scale * planarHopping ((q : ℝ) * ℓ a) -
--         coulombHoppingTarget freq τ (K a) ((q : ℝ) * ℓ a)| ≤ ε)
--       (a : GlobalEdge d)
--       (hne : (finalGraph d.bonds W G).left a ≠ (finalGraph d.bonds W G).right a) :
--       let r := dist (point d P q ℓ ((finalGraph d.bonds W G).left a))
--         (point d P q ℓ ((finalGraph d.bonds W G).right a))
--       |scale * planarHopping r - coulombHoppingTarget freq τ (K a) r| ≤
--         ε + (scale * (planarHoppingLipschitzConstant : ℝ) +
--           coulombTargetLipschitzConstant freq τ (K a)) * ((q : ℝ) * (72 * ((P : ℝ) + 1)⁻¹))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.ContactPoint`, `OAI.ContinuumCoulomb.SquareLatticeHeisenberg`, `OAI.ContinuumCoulomb.ContactMediator.GlobalEdge`, `OAI.ContinuumCoulomb.SquareLatticeHeisenberg.bonds` and `OAI.ContinuumCoulomb.MediatorIteration.Bonds` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.contactLengthTolerance` (definitions bundle `OAIQ092A003` of this split); `OAI.ContinuumCoulomb.coulombHoppingTarget`, `OAI.ContinuumCoulomb.coulombTargetLipschitzConstant`, `OAI.ContinuumCoulomb.localDualMass`, `OAI.ContinuumCoulomb.planarHopping`, `OAI.ContinuumCoulomb.planarHoppingLipschitzConstant`, `OAI.ContinuumCoulomb.ContactCalibratedGeometry.point` and `OAI.ContinuumCoulomb.MediatorIteration.finalGraph` (definitions bundle `OAIQ092A004` of this split); `OAI.ContinuumCoulomb.localLeakageBound` (definitions bundle `OAIQ092A007` of this split).
--
--   **Used by.** The proof of `OAI.ContinuumCoulomb.SourceNuclearProgram.exists_indexed_matrix_offsets` of this split imports it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ContactCalibratedGeometry.lean (declaration OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual)

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
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAIQ092A004
import Definitions.Def_OAIQ092A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ContinuumCoulomb.ContactCalibratedGeometry
open ContactMediator MediatorIteration
open scoped BigOperators

theorem calibrated_edge_residual (d : SquareLatticeHeisenberg) (W G P : ℕ)
    {q : ℚ} (hq : 0 < q) (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    {freq D scale τ ε : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2)
    (hDq : D ≤ (9 / 10 : ℝ) * q) (hscale : 0 ≤ scale) (hτ : 0 ≤ τ)
    (K : GlobalEdge d → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hres : ∀ a, |scale * planarHopping ((q : ℝ) * ℓ a) -
      coulombHoppingTarget freq τ (K a) ((q : ℝ) * ℓ a)| ≤ ε)
    (a : GlobalEdge d)
    (hne : (finalGraph d.bonds W G).left a ≠ (finalGraph d.bonds W G).right a) :
    let r := dist (point d P q ℓ ((finalGraph d.bonds W G).left a))
      (point d P q ℓ ((finalGraph d.bonds W G).right a))
    |scale * planarHopping r - coulombHoppingTarget freq τ (K a) r| ≤
      ε + (scale * (planarHoppingLipschitzConstant : ℝ) +
        coulombTargetLipschitzConstant freq τ (K a)) * ((q : ℝ) * (72 * ((P : ℝ) + 1)⁻¹)) := by
  sorry

end ContinuumCoulomb.ContactCalibratedGeometry

end

end OAI
end
