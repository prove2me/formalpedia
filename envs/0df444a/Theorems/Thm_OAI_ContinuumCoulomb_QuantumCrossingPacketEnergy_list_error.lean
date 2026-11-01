-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_QuantumCrossingPacketEnergy_list_error
-- name    : OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:13:07.80655+00:00
-- url     : https://prove2.me/theorems/d109b3df-eeef-4cb5-87a8-d1cf4ab056b7
-- title:
--   OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumCrossingPacketEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumCrossingPacketEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy`, with `open QuantumCrossingListBlock MediatorListProgram QuantumCrossingSelectProgram`, `open scoped Classical`):
--
--   ```lean
--   theorem list_error (n : ℕ) (bs : List Bond) (c : ℚ)
--       (hb : SourceBondLists.bounded n bs) (hn : ∀ e ∈ bs, e.1≠e.2.1)
--       {r : ℕ} (site : Fin r → Fin 4 → Fin n)
--       (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
--       {N : ℚ} (hN : 0<N) :
--       |energy (QuantumCrossingListLayer.value
--         (QuantumCrossingSelectProgram.value (N,(n,bs,c),List.ofFn (encodedSites site))))-
--         energy (n,bs,c)|≤1/(N:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.MediatorListProgram.Bond` and `OAI.ContinuumCoulomb.SourceBondLists.bounded` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.QuantumCrossingListBlock.Sites` and `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.encodedSites` (definitions bundle `OAIQ092A002` of this split); `OAI.ContinuumCoulomb.QuantumListPathStep.Output` (definitions bundle `OAIQ092A005` of this split); `OAI.ContinuumCoulomb.QuantumCrossingListLayer.value`, `OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.energy` and `OAI.ContinuumCoulomb.QuantumCrossingSelectProgram.value` (definitions bundle `OAIQ092A008` of this split).
--
--   **Used by.** The proofs of `OAI.ContinuumCoulomb.QuantumFinalRoutingProgram.spatial_energy_error` and `OAI_ContinuumCoulomb_QuantumSpatialCrossingProgram_energy_error` of this split import it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Quantum/QuantumCrossingPacketEnergy.lean (declaration OAI.ContinuumCoulomb.QuantumCrossingPacketEnergy.list_error)

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
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
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
import Definitions.Def_OAIQ092A008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPacketEnergy
open QuantumCrossingListBlock MediatorListProgram QuantumCrossingSelectProgram
open scoped Classical

theorem list_error (n : ℕ) (bs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n bs) (hn : ∀ e ∈ bs, e.1≠e.2.1)
    {r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
    {N : ℚ} (hN : 0<N) :
    |energy (QuantumCrossingListLayer.value
      (QuantumCrossingSelectProgram.value (N,(n,bs,c),List.ofFn (encodedSites site))))-
      energy (n,bs,c)|≤1/(N:ℝ) := by
  sorry

end ContinuumCoulomb.QuantumCrossingPacketEnergy

end

end OAI
end
