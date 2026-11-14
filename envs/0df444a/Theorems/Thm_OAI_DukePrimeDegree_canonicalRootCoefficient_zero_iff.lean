-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_canonicalRootCoefficient_zero_iff
-- name    : OAI.DukePrimeDegree.canonicalRootCoefficient_zero_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:37:40.122996+00:00
-- url     : https://prove2.me/theorems/12cd11e0-86e5-47da-8806-fb434b90f399
-- title:
--   OAI.DukePrimeDegree.canonicalRootCoefficient_zero_iff: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.canonicalRootCoefficient_zero_iff` of [lean/OAI/NumberTheory/DukePrimeDegree/Geometry/CanonicalRootBasic.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/CanonicalRootBasic.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open PrimeDegreePackets`):
--
--   ```lean
--   lemma canonicalRootCoefficient_zero_iff (i j : Fin (d + 1)) (hij : i ≠ j) :
--       canonicalRootCoefficient d μ i j = 0 ↔
--         ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.canonicalRootCoefficient` and `OAI.PrimeDegreePackets.intrinsicRootLeaf` (definitions bundle `OAIQ244Duke022` of this split); `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.DukePrimeDegree.eklPrimeInput_of_regular_entropy_upper_bounds`, `OAI.DukePrimeDegree.no_two_step_positive_roots_of_no_invariant_root` and `OAI.DukePrimeDegree.rootInvarianceRelation_symmetric_of_regular_tests` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/CanonicalRootBasic.lean (declaration OAI.DukePrimeDegree.canonicalRootCoefficient_zero_iff)

import Mathlib
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke022

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

lemma canonicalRootCoefficient_zero_iff (i j : Fin (d + 1)) (hij : i ≠ j) :
    canonicalRootCoefficient d μ i j = 0 ↔
      ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  sorry

end DukePrimeDegree

end

end OAI
end
