-- Prove2me | Theorems.Thm_OAI_ExactQuantumFactoring_Completion_orderSuccess_lower
-- name    : OAI.ExactQuantumFactoring.Completion.orderSuccess_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:05:41.278643+00:00
-- url     : https://prove2.me/theorems/53f5b337-33e1-4256-bc2e-0f6a9186cf74
-- title:
--   OAI.ExactQuantumFactoring.Completion.orderSuccess_lower: intermediate lemma from OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ExactQuantumFactoring.Completion.orderSuccess_lower` of [lean/OAI/Computability/QuantumFactoring/TransitionEqualization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/TransitionEqualization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ExactQuantumFactoring.Completion`, with `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open Exactness RepeatedTrials OrderTrial`):
--
--   ```lean
--   lemma orderSuccess_lower {w n s : ℕ} (hn : 128 ≤ n) (hs : 2^(s+2)=(2^n)^16)
--       (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
--       (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
--       (hdB : orderOf u<2^n) : 1-1/(2:ℚ)^(2*n) ≤ orderSuccess (orderOf u) (n^5)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ExactQuantumFactoring.bitsValue` and `OAI.ExactQuantumFactoring.Completion.orderSuccess` (definitions bundle `OAIQ222A001` of this split); `OAI.ExactQuantumFactoring.Basis` (the published bundle `Def_ExactQuantumFactoring`).
--
--   **Used by.** The proof of `OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_spec` of this split imports it.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/TransitionEqualization.lean (declaration OAI.ExactQuantumFactoring.Completion.orderSuccess_lower)

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
import Definitions.Def_OAIQ222A001

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
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial

namespace Completion

lemma orderSuccess_lower {w n s : ℕ} (hn : 128 ≤ n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) : 1-1/(2:ℚ)^(2*n) ≤ orderSuccess (orderOf u) (n^5) := by
  sorry

end Completion
end ExactQuantumFactoring

end

end OAI
end
