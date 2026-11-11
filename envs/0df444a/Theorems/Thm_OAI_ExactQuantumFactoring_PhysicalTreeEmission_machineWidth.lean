-- Prove2me | Theorems.Thm_OAI_ExactQuantumFactoring_PhysicalTreeEmission_machineWidth
-- name    : OAI.ExactQuantumFactoring.PhysicalTreeEmission.machineWidth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:14:43.447162+00:00
-- url     : https://prove2.me/theorems/19ac3cd2-c95f-4549-8f5b-5eb364f809a9
-- title:
--   OAI.ExactQuantumFactoring.PhysicalTreeEmission.machineWidth: intermediate lemma from OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ExactQuantumFactoring.PhysicalTreeEmission.machineWidth` of [lean/OAI/Computability/QuantumFactoring/PhysicalTreeEmission.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/PhysicalTreeEmission.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ExactQuantumFactoring.PhysicalTreeEmission`, with `open BitStackProgram BitStackProgram.Emits NetworkEmission CircuitEmission`):
--
--   ```lean
--   lemma machineWidth (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).width (t x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ExactQuantumFactoring.BitStackProgram.unaryCode` (definitions bundle `OAIQ222A000` of this split); `OAI.ExactQuantumFactoring.PhysicalTree.configWidth` (definitions bundle `OAIQ222A001` of this split); `OAI.ExactQuantumFactoring.BitStackProgram.Emits` (definitions bundle `OAIQ222A003` of this split); `OAI.ExactQuantumFactoring.NodeMachine.width` and `OAI.ExactQuantumFactoring.PhysicalTree.machine` (definitions bundle `OAIQ222A004` of this split).
--
--   **Used by.** The proofs of `OAI.ExactQuantumFactoring.PhysicalTreeEmission.lastNode`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.listFilterVars`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedFlag`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedHistory`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedPad`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.previous`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterCoin`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterGuessFlag`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterOrd`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterOutput`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterProgram`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterRare`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterWidth`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedCanonicalList`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedComponentOrder`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedGoodList`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedOrder`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedOrderPhi` and `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedSplitFilter` of this split import it.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/QuantumFactoring/PhysicalTreeEmission.lean (declaration OAI.ExactQuantumFactoring.PhysicalTreeEmission.machineWidth)

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
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma machineWidth (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).width (t x)):= by
  sorry
end ExactQuantumFactoring.PhysicalTreeEmission

end

end OAI
end
