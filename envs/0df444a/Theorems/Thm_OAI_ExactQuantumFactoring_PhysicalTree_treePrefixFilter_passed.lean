-- Prove2me | Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTree_treePrefixFilter_passed
-- name    : OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:13:01.974396+00:00
-- url     : https://prove2.me/theorems/890574b0-9804-4e32-ac47-9d183672b0c5
-- title:
--   OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed: intermediate lemma from OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed` of [lean/OAI/Computability/QuantumFactoring/RetainedTreeFilter.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/RetainedTreeFilter.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ExactQuantumFactoring.PhysicalTree`, with `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open BooleanNetwork BitArithmetic OrderTrial`):
--
--   ```lean
--   lemma treePrefixFilter_passed {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
--       (T s : ℕ) (h : NodeMachine.Trace n T) (r : NodeMachine.Trace n s)
--       (raw : BooleanNetwork ((machine n).width T) ((machine n).width s))
--       (hc : CompleteLog n N ((machine n).dataLog (initialQueue n N) T h))
--       (hv : (machine n).verified (initialQueue n N) s r)
--       (hsub : ∀ a∈(machine n).dataLog (initialQueue n N) s r,
--         a∈(machine n).dataLog (initialQueue n N) T h)
--       (hr : raw.eval ((machine n).encoded (initialQueue n N) T h)=
--         (machine n).encoded (initialQueue n N) s r) :
--       ((machine n).treePrefixFilter (by omega) T s raw).eval
--         ((machine n).encoded (initialQueue n N) T h) 0=true ↔
--         (machine n).passed (initialQueue n N) s r
--   ```
--
--   **Definitions.** The statement is written with `OAI.ExactQuantumFactoring.BooleanNetwork` and `OAI.ExactQuantumFactoring.BooleanNetwork.eval` (definitions bundle `OAIQ222A000` of this split); `OAI.ExactQuantumFactoring.PhysicalTree.CompleteLog` and `OAI.ExactQuantumFactoring.PhysicalTree.configWidth` (definitions bundle `OAIQ222A001` of this split); `OAI.ExactQuantumFactoring.NodeMachine.Trace`, `OAI.ExactQuantumFactoring.NodeMachine.dataLog`, `OAI.ExactQuantumFactoring.NodeMachine.encoded`, `OAI.ExactQuantumFactoring.NodeMachine.passed`, `OAI.ExactQuantumFactoring.NodeMachine.treePrefixFilter`, `OAI.ExactQuantumFactoring.NodeMachine.verified`, `OAI.ExactQuantumFactoring.NodeMachine.width`, `OAI.ExactQuantumFactoring.PhysicalTree.initialQueue` and `OAI.ExactQuantumFactoring.PhysicalTree.machine` (definitions bundle `OAIQ222A004` of this split).
--
--   **Used by.** The proof of `OAI.ExactQuantumFactoring.PhysicalTree.quarterFlag_eval` of this split imports it.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/RetainedTreeFilter.lean (declaration OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed)

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
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

lemma treePrefixFilter_passed {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (T s : ℕ) (h : NodeMachine.Trace n T) (r : NodeMachine.Trace n s)
    (raw : BooleanNetwork ((machine n).width T) ((machine n).width s))
    (hc : CompleteLog n N ((machine n).dataLog (initialQueue n N) T h))
    (hv : (machine n).verified (initialQueue n N) s r)
    (hsub : ∀ a∈(machine n).dataLog (initialQueue n N) s r,
      a∈(machine n).dataLog (initialQueue n N) T h)
    (hr : raw.eval ((machine n).encoded (initialQueue n N) T h)=
      (machine n).encoded (initialQueue n N) s r) :
    ((machine n).treePrefixFilter (by omega) T s raw).eval
      ((machine n).encoded (initialQueue n N) T h) 0=true ↔
      (machine n).passed (initialQueue n N) s r := by
  sorry

end PhysicalTree
end ExactQuantumFactoring

end

end OAI
end
