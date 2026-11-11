-- Prove2me | Theorems.Thm_OAI_ExactQuantumFactoring_OrderTrial_orderResult_mass
-- name    : OAI.ExactQuantumFactoring.OrderTrial.orderResult_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:13:18.753422+00:00
-- url     : https://prove2.me/theorems/657ca13e-585d-4cb7-b467-f42b96dc6a71
-- title:
--   OAI.ExactQuantumFactoring.OrderTrial.orderResult_mass: intermediate lemma from OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ExactQuantumFactoring.OrderTrial.orderResult_mass` of [lean/OAI/Computability/QuantumFactoring/OrderTransition.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/OrderTransition.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ExactQuantumFactoring.OrderTrial`, with `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open scoped BigOperators`, `open Exactness RepeatedTrials`):
--
--   ```lean
--   theorem orderResult_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
--       (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
--       (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
--       (hdB : orderOf u<2^n) (K : ℕ) :
--       outcomeMass (fun x => orderResult s n a m K x=orderOf u) (tensorState (rawState s n a m) K)=
--         1-(1-(Nat.totient (orderOf u):ℝ)*(prescribedMass (orderOf u):ℝ))^K
--   ```
--
--   **Definitions.** The statement is written with `OAI.ExactQuantumFactoring.bitsValue`, `OAI.ExactQuantumFactoring.Exactness.outcomeMass`, `OAI.ExactQuantumFactoring.OrderSample.width`, `OAI.ExactQuantumFactoring.OrderTrial.prescribedMass`, `OAI.ExactQuantumFactoring.OrderTrial.retentionBits` and `OAI.ExactQuantumFactoring.RepeatedTrials.tensorState` (definitions bundle `OAIQ222A001` of this split); `OAI.ExactQuantumFactoring.OrderTrial.Guesses`, `OAI.ExactQuantumFactoring.OrderTrial.Raw`, `OAI.ExactQuantumFactoring.OrderTrial.orderResult` and `OAI.ExactQuantumFactoring.OrderTrial.rawState` (definitions bundle `OAIQ222A004` of this split); `OAI.ExactQuantumFactoring.Basis` (the published bundle `Def_ExactQuantumFactoring`).
--
--   **Used by.** The proofs of `OAI.ExactQuantumFactoring.Completion.orderSuccess_lower` and `OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_spec` of this split import it.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/OrderTransition.lean (declaration OAI.ExactQuantumFactoring.OrderTrial.orderResult_mass)

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

attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare _root_.OAI.ExactQuantumFactoring.FixedSplit.rawFintype _root_.OAI.ExactQuantumFactoring.NodeMachine.traceFintype _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype _root_.OAI.ExactQuantumFactoring.PhysicalListSlots.resultFintype _root_.OAI.ExactQuantumFactoring.SplitMachine.traceFintype
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

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness RepeatedTrials

theorem orderResult_mass {w n s : ℕ} (hn : 1≤n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (K : ℕ) :
    outcomeMass (fun x => orderResult s n a m K x=orderOf u) (tensorState (rawState s n a m) K)=
      1-(1-(Nat.totient (orderOf u):ℝ)*(prescribedMass (orderOf u):ℝ))^K := by
  sorry

end ExactQuantumFactoring.OrderTrial

end

end OAI
end
