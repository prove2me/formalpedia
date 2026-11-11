-- Prove2me | Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalNode_decoded_value
-- name    : OAI.ExactQuantumFactoring.PhysicalNode.decoded_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:14:19.592195+00:00
-- url     : https://prove2.me/theorems/74c12c8c-e4d5-45e8-8c27-5c2542431c5e
-- title:
--   OAI.ExactQuantumFactoring.PhysicalNode.decoded_value: intermediate lemma from OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ExactQuantumFactoring.PhysicalNode.decoded_value` of [lean/OAI/Computability/QuantumFactoring/NodeSplitMachine.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/NodeSplitMachine.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ExactQuantumFactoring.PhysicalNode`, with `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open BooleanNetwork BitArithmetic`):
--
--   ```lean
--   lemma decoded_value {n : ℕ} (hn : 2 ≤ n) (q : Basis n) (r : FixedSplit.Raw n)
--       (hq : 2 ≤ (bitsValue q).toNat) :
--       (bitsValue (decoded q r)).toNat=FixedSplit.divisor q r
--   ```
--
--   **Definitions.** The statement is written with `OAI.ExactQuantumFactoring.bitsValue` (definitions bundle `OAIQ222A001` of this split); `OAI.ExactQuantumFactoring.FixedSplit.Raw`, `OAI.ExactQuantumFactoring.FixedSplit.divisor` and `OAI.ExactQuantumFactoring.PhysicalNode.decoded` (definitions bundle `OAIQ222A004` of this split); `OAI.ExactQuantumFactoring.Basis` (the published bundle `Def_ExactQuantumFactoring`).
--
--   **Used by.** The proofs of `OAI.ExactQuantumFactoring.PhysicalTree.accepted_iff_passed` and `OAI.ExactQuantumFactoring.PhysicalTree.quarterFlag_eval` of this split import it.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/NodeSplitMachine.lean (declaration OAI.ExactQuantumFactoring.PhysicalNode.decoded_value)

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

attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open BooleanNetwork BitArithmetic
namespace PhysicalNode

lemma decoded_value {n : ℕ} (hn : 2 ≤ n) (q : Basis n) (r : FixedSplit.Raw n)
    (hq : 2 ≤ (bitsValue q).toNat) :
    (bitsValue (decoded q r)).toNat=FixedSplit.divisor q r := by
  sorry

end PhysicalNode
end ExactQuantumFactoring

end

end OAI
end
