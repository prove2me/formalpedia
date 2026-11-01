-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_QuantumHistorySourceProgram_history_error
-- name    : OAI.ContinuumCoulomb.QuantumHistorySourceProgram.history_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:45:26.630242+00:00
-- url     : https://prove2.me/theorems/b58876ed-f984-48b3-9981-38b4e30b9f5c
-- title:
--   OAI.ContinuumCoulomb.QuantumHistorySourceProgram.history_error: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.QuantumHistorySourceProgram.history_error` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumHistoryRoutedEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumHistoryRoutedEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb.QuantumHistorySourceProgram`, with `open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram`, `open QuantumAlgebraicHistory`):
--
--   ```lean
--   theorem history_error (c : QMACircuit) (hc : c.WellFormed) :
--       |QuantumListSchedule.energy (routedState c).1-
--         (qmaOrderedHistoryModel (qmaPreparedCircuit c) (qmaNonemptyCircuit_sparse_pos c)).energy| ≤
--         ((totalRounds:ℝ)+9)/(precision c:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.QuantumRouteCode.Pair` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.QuantumHistorySpatial.totalRounds` (definitions bundle `OAIQ092A002` of this split); `OAI.ContinuumCoulomb.QMARealLocalModel.energy`, `OAI.ContinuumCoulomb.QuantumListSchedule.State` and `OAI.ContinuumCoulomb.QuantumListSchedule.energy` (definitions bundle `OAIQ092A006` of this split); `OAI.ContinuumCoulomb.qmaOrderedHistoryModel` and `OAI.ContinuumCoulomb.qmaPreparedCircuit` (definitions bundle `OAIQ092A008` of this split); `OAI.ContinuumCoulomb.qmaNonemptyCircuit_sparse_pos`, `OAI.ContinuumCoulomb.QuantumHistoryPreparedProgram.precision` and `OAI.ContinuumCoulomb.QuantumHistorySourceProgram.routedState` (definitions bundle `OAIQ092A010` of this split); `OAI.ContinuumCoulomb.QMACircuit` and `OAI.ContinuumCoulomb.QMACircuit.WellFormed` (the published bundle `Def_ContinuumCoulombHardness`).
--
--   **Used by.** The proofs of `OAI_ContinuumCoulomb_QuantumHistorySourceProgram_routed_accepting`, `OAI_ContinuumCoulomb_QuantumHistorySourceProgram_routed_rejecting` and `OAI.ContinuumCoulomb.publishedCMPHardness` of this split import it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumHistoryRoutedEnergy.lean (declaration OAI.ContinuumCoulomb.QuantumHistorySourceProgram.history_error)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.UpperLower.Basic
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
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram
open QuantumAlgebraicHistory

theorem history_error (c : QMACircuit) (hc : c.WellFormed) :
    |QuantumListSchedule.energy (routedState c).1-
      (qmaOrderedHistoryModel (qmaPreparedCircuit c) (qmaNonemptyCircuit_sparse_pos c)).energy| ≤
      ((totalRounds:ℝ)+9)/(precision c:ℝ) := by
  sorry

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
end
