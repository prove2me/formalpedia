-- Prove2me | Theorems.Thm_OAI_ExactQuantumFactoring_NodeMachine_retainedOrderFilter_exact
-- name    : OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter_exact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:11:48.81729+00:00
-- url     : https://prove2.me/theorems/c454d29f-8dee-4467-948e-a5ebb3bbbe9c
-- title:
--   OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter_exact: intermediate lemma from OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter_exact` of [lean/OAI/Computability/QuantumFactoring/RetainedOrderTest.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/RetainedOrderTest.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ExactQuantumFactoring.NodeMachine`, with `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open BooleanNetwork BitArithmetic OrderTrial`):
--
--   ```lean
--   theorem retainedOrderFilter_exact {N P : ℕ} (hn : 2 ≤ n) (t : ℕ)
--       (a m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
--       (x : Basis c) (h : Trace n t) (r : OrderSlots.Result n)
--       (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
--       (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
--       (hd : 2 ≤ (bitsValue (m.eval (M.encoded x t h))).toNat)
--       (hdiv : (bitsValue (m.eval (M.encoded x t h))).toNat∣P)
--       (hr : raw.eval (M.encoded x t h)=OrderSlots.layout n r) :
--       (M.retainedOrderFilter t a m raw).eval (M.encoded x t h) 0=true ↔
--         dataOrderPassed (trueData P) (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h)) r
--   ```
--
--   **Definitions.** The statement is written with `OAI.ExactQuantumFactoring.BooleanNetwork` and `OAI.ExactQuantumFactoring.BooleanNetwork.eval` (definitions bundle `OAIQ222A000` of this split); `OAI.ExactQuantumFactoring.bitsValue`, `OAI.ExactQuantumFactoring.trueData`, `OAI.ExactQuantumFactoring.OrderSlots.width` and `OAI.ExactQuantumFactoring.PhysicalTree.CompleteLog` (definitions bundle `OAIQ222A001` of this split); `OAI.ExactQuantumFactoring.NodeMachine`, `OAI.ExactQuantumFactoring.dataOrderPassed`, `OAI.ExactQuantumFactoring.NodeMachine.Trace`, `OAI.ExactQuantumFactoring.NodeMachine.dataLog`, `OAI.ExactQuantumFactoring.NodeMachine.encoded`, `OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter`, `OAI.ExactQuantumFactoring.NodeMachine.width`, `OAI.ExactQuantumFactoring.OrderSlots.Result` and `OAI.ExactQuantumFactoring.OrderSlots.layout` (definitions bundle `OAIQ222A004` of this split); `OAI.ExactQuantumFactoring.Basis` (the published bundle `Def_ExactQuantumFactoring`).
--
--   **Used by.** The proof of `OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed` of this split imports it.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/RetainedOrderTest.lean (declaration OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter_exact)

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
import Definitions.Def_ExactQuantumFactoring
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

theorem retainedOrderFilter_exact {N P : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (a m : BooleanNetwork (M.width t) n) (raw : BooleanNetwork (M.width t) (OrderSlots.width n))
    (x : Basis c) (h : Trace n t) (r : OrderSlots.Result n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ (bitsValue (m.eval (M.encoded x t h))).toNat)
    (hdiv : (bitsValue (m.eval (M.encoded x t h))).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=OrderSlots.layout n r) :
    (M.retainedOrderFilter t a m raw).eval (M.encoded x t h) 0=true ↔
      dataOrderPassed (trueData P) (a.eval (M.encoded x t h)) (m.eval (M.encoded x t h)) r := by
  sorry
end NodeMachine
end ExactQuantumFactoring

end

end OAI
end
