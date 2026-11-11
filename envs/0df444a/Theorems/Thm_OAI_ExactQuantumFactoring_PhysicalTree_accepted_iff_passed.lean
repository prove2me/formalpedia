-- Prove2me | Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTree_accepted_iff_passed
-- name    : OAI.ExactQuantumFactoring.PhysicalTree.accepted_iff_passed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:14:23.688393+00:00
-- url     : https://prove2.me/theorems/be253eb9-03ae-4263-b3b4-0c7548d2c0ad
-- title:
--   OAI.ExactQuantumFactoring.PhysicalTree.accepted_iff_passed: intermediate lemma from OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ExactQuantumFactoring.PhysicalTree.accepted_iff_passed` of [lean/OAI/Computability/QuantumFactoring/RetrospectiveTree.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/RetrospectiveTree.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ExactQuantumFactoring.PhysicalTree`, with `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree`):
--
--   ```lean
--   theorem accepted_iff_passed {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
--       (r : NodeMachine.Trace n (2*n^2)) :
--       accepted (N:=N) (by omega) r ↔ (machine n).passed (initialQueue n N) (2*n^2) r
--   ```
--
--   **Definitions.** The statement is written with `OAI.ExactQuantumFactoring.PhysicalTree.configWidth` (definitions bundle `OAIQ222A001` of this split); `OAI.ExactQuantumFactoring.NodeMachine.Trace`, `OAI.ExactQuantumFactoring.NodeMachine.passed`, `OAI.ExactQuantumFactoring.PhysicalTree.accepted`, `OAI.ExactQuantumFactoring.PhysicalTree.initialQueue` and `OAI.ExactQuantumFactoring.PhysicalTree.machine` (definitions bundle `OAIQ222A004` of this split).
--
--   **Used by.** The proofs of `OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_spec` and `OAI.ExactQuantumFactoring.PhysicalTree.quarterFlag_eval` of this split import it.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/RetrospectiveTree.lean (declaration OAI.ExactQuantumFactoring.PhysicalTree.accepted_iff_passed)

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_OAIQ222A004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree
namespace PhysicalTree

theorem accepted_iff_passed {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (r : NodeMachine.Trace n (2*n^2)) :
    accepted (N:=N) (by omega) r ↔ (machine n).passed (initialQueue n N) (2*n^2) r := by
  sorry

end PhysicalTree
end ExactQuantumFactoring

end

end OAI
end
