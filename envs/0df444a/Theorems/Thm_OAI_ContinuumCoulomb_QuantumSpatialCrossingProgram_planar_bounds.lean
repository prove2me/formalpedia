-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_QuantumSpatialCrossingProgram_planar_bounds
-- name    : OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.planar_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:47:28.331673+00:00
-- url     : https://prove2.me/theorems/425fd0c7-d540-4719-87da-e1a7a523de25
-- title:
--   OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.planar_bounds: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.planar_bounds` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumSpatialPlanarBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumSpatialPlanarBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram`, with `open QuantumForkList QuantumCrossingSelectProgram QuantumCoefficientPrograms`, `open scoped Classical`):
--
--   ```lean
--   theorem planar_bounds {rows width A D : ℕ} (I : SpatialInput rows width A D)
--       (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 ≤ N) {L T : ℕ}
--       (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : I.model.exchangeGraph.CoefficientBound L)
--       (hn : ∀ e ∈ (value A D (N,QuantumSpatialInputTape.input I)).1.1.2.1, e.1 ≠ e.2.1) :
--       let K := QuantumSpatialPortProgram.rounds A D
--       let m := 3^K*Fintype.card I.model.Term
--       let r := (I.model.portRouteData hA I.model_degree).crossingCells.card
--       let B := iterated (Fintype.card I.model.Term) L T K
--       (QuantumPlanarTapeGeometry.graph (value A D (N,QuantumSpatialInputTape.input I)) hn).CoefficientBound
--         ((m+9*r+1)*crossingCoefficient m r ((m+1)*B) T) ∧
--       Fintype.card (QuantumPlanarTapeGeometry.graph
--         (value A D (N,QuantumSpatialInputTape.input I)) hn).Edge ≤ m+9*r
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.MediatorListProgram.Bond`, `OAI.ContinuumCoulomb.QMARationalExchangeGraph`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel`, `OAI.ContinuumCoulomb.QuantumRouteCode.Pair` and `OAI.ContinuumCoulomb.QuantumRoutingTable.Table` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.QuantumCoefficientPrograms.crossingCoefficient`, `OAI.ContinuumCoulomb.QuantumCoefficientPrograms.iterated`, `OAI.ContinuumCoulomb.QuantumForkList.spatialDensity` and `OAI.ContinuumCoulomb.QuantumSpatialPortProgram.rounds` (definitions bundle `OAIQ092A002` of this split); `OAI.ContinuumCoulomb.QMAPortRouteData.crossingCells` and `OAI.ContinuumCoulomb.QuantumListPathStep.Output` (definitions bundle `OAIQ092A005` of this split); `OAI.ContinuumCoulomb.QMARationalExchangeGraph.CoefficientBound`, `OAI.ContinuumCoulomb.QMASpatialExchangeModel.exchangeGraph`, `OAI.ContinuumCoulomb.QuantumForkGridProgram.PreparedInput` and `OAI.ContinuumCoulomb.QuantumForkList.SpatialInput` (definitions bundle `OAIQ092A006` of this split); `OAI.ContinuumCoulomb.QMASpatialExchangeModel.portRouteData` (definitions bundle `OAIQ092A008` of this split); `OAI.ContinuumCoulomb.QuantumSpatialInputTape.input` (definitions bundle `OAIQ092A009` of this split); `OAI.ContinuumCoulomb.QuantumPlanarTapeGeometry.graph`, `OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.value`, `OAI.ContinuumCoulomb.QuantumForkList.SpatialInput.model` and `OAI.ContinuumCoulomb.QuantumForkList.SpatialInput.model_degree` (definitions bundle `OAIQ092A010` of this split).
--
--   **Used by.** The proof of `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_polynomialPromise` of this split imports it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumSpatialPlanarBounds.lean (declaration OAI.ContinuumCoulomb.QuantumSpatialCrossingProgram.planar_bounds)

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
import Definitions.Def_OAIQ092A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialCrossingProgram
open QuantumForkList QuantumCrossingSelectProgram QuantumCoefficientPrograms
open scoped Classical

theorem planar_bounds {rows width A D : ℕ} (I : SpatialInput rows width A D)
    (hA : 0 < spatialDensity A D) {N : ℚ} (hN : 0 ≤ N) {L T : ℕ}
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : I.model.exchangeGraph.CoefficientBound L)
    (hn : ∀ e ∈ (value A D (N,QuantumSpatialInputTape.input I)).1.1.2.1, e.1 ≠ e.2.1) :
    let K := QuantumSpatialPortProgram.rounds A D
    let m := 3^K*Fintype.card I.model.Term
    let r := (I.model.portRouteData hA I.model_degree).crossingCells.card
    let B := iterated (Fintype.card I.model.Term) L T K
    (QuantumPlanarTapeGeometry.graph (value A D (N,QuantumSpatialInputTape.input I)) hn).CoefficientBound
      ((m+9*r+1)*crossingCoefficient m r ((m+1)*B) T) ∧
    Fintype.card (QuantumPlanarTapeGeometry.graph
      (value A D (N,QuantumSpatialInputTape.input I)) hn).Edge ≤ m+9*r := by
  sorry

end ContinuumCoulomb.QuantumSpatialCrossingProgram

end

end OAI
end
