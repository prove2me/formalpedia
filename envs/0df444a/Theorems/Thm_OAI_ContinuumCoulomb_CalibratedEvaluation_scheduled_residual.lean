-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_CalibratedEvaluation_scheduled_residual
-- name    : OAI.ContinuumCoulomb.CalibratedEvaluation.scheduled_residual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:53:32.306994+00:00
-- url     : https://prove2.me/theorems/77984fce-bc60-4e6e-a9ef-e350ebba6ee5
-- title:
--   OAI.ContinuumCoulomb.CalibratedEvaluation.scheduled_residual: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.CalibratedEvaluation.scheduled_residual` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/CalibratedBisectionSchedule.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/CalibratedBisectionSchedule.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb.CalibratedEvaluation`):
--
--   ```lean
--   theorem scheduled_residual (rho : ℕ) (hrho : 0 < rho) (e : Environment) (a b : ℚ)
--       (hK : (0 : ℚ) ≤ e.2.2.2) (hKN : (e.2.2.2 : ℝ) ≤ e.1.1)
--       (hτ : (0 : ℚ) ≤ e.2.2.1) (hτ1 : e.2.2.1 ≤ 1) (hab : a ≤ b)
--       (haN : -(e.1.1 : ℝ) ≤ a) (hbN : (b : ℝ) ≤ e.1.1)
--       (ha : 0 ≤ residual rho e a) (hb : residual rho e b ≤ 0)
--       (hgap : ∀ r ∈ Set.Icc (a : ℝ) b,
--         localizedGramConstant (GaussianFrequency.frequency rho) ≤
--           localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
--             localizedCoulombProfile (GaussianFrequency.frequency rho) r) :
--       |residual rho e (scheduledValue rho e a b)| ≤ ((e.1.2 : ℝ) + 1)⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.GaussianFrequency.frequency` (definitions bundle `OAIQ092A000` of this split); `OAI.ContinuumCoulomb.CalibratedEvaluation.Environment` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.localizedCoulombProfile`, `OAI.ContinuumCoulomb.localizedGramConstant`, `OAI.ContinuumCoulomb.CalibratedEvaluation.residual` and `OAI.ContinuumCoulomb.CalibratedEvaluation.scheduledValue` (definitions bundle `OAIQ092A004` of this split).
--
--   **Used by.** The proof of `OAI.ContinuumCoulomb.PrefactorSourceContactProgram.exists_source_calibration` of this split imports it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/CalibratedBisectionSchedule.lean (declaration OAI.ContinuumCoulomb.CalibratedEvaluation.scheduled_residual)

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

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation

theorem scheduled_residual (rho : ℕ) (hrho : 0 < rho) (e : Environment) (a b : ℚ)
    (hK : (0 : ℚ) ≤ e.2.2.2) (hKN : (e.2.2.2 : ℝ) ≤ e.1.1)
    (hτ : (0 : ℚ) ≤ e.2.2.1) (hτ1 : e.2.2.1 ≤ 1) (hab : a ≤ b)
    (haN : -(e.1.1 : ℝ) ≤ a) (hbN : (b : ℝ) ≤ e.1.1)
    (ha : 0 ≤ residual rho e a) (hb : residual rho e b ≤ 0)
    (hgap : ∀ r ∈ Set.Icc (a : ℝ) b,
      localizedGramConstant (GaussianFrequency.frequency rho) ≤
        localizedCoulombProfile (GaussianFrequency.frequency rho) 0 -
          localizedCoulombProfile (GaussianFrequency.frequency rho) r) :
    |residual rho e (scheduledValue rho e a b)| ≤ ((e.1.2 : ℝ) + 1)⁻¹ := by
  sorry

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
end
