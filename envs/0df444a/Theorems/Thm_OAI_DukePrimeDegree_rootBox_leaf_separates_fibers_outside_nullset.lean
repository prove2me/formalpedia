-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_rootBox_leaf_separates_fibers_outside_nullset
-- name    : OAI.DukePrimeDegree.rootBox_leaf_separates_fibers_outside_nullset
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:41:34.078954+00:00
-- url     : https://prove2.me/theorems/c244ca6e-5ba3-49d3-95d4-9a047204f672
-- title:
--   OAI.DukePrimeDegree.rootBox_leaf_separates_fibers_outside_nullset: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.rootBox_leaf_separates_fibers_outside_nullset` of [lean/OAI/NumberTheory/DukePrimeDegree/Geometry/LeafBoxSeparation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/LeafBoxSeparation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set Filter MeasureTheory`, `open scoped Topology Classical`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem rootBox_leaf_separates_fibers_outside_nullset
--       (d : ℕ) {i j k : Fin (d + 1)} (hij : i ≠ j)
--       (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
--       [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
--       (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
--         (Matrix.SpecialLinearGroup.transvection hij a)) = μ)
--       (A : RootBox hij k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) :
--       ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
--         ∀ z ∈ A.domain, ∀ w ∈ A.domain,
--           rootQuotientParametrization hij z ∉ N →
--           rootQuotientParametrization hij w ∉ N → z.1 = w.1 →
--           intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) =
--             intrinsicRootLeaf hij μ (rootQuotientParametrization hij w) → z = w
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.RootSlice`, `OAI.PrimeDegreePackets.diagonalLogAction` and `OAI.PrimeDegreePackets.rootLeafWindow` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.RootBox`, `OAI.PrimeDegreePackets.intrinsicRootLeaf`, `OAI.PrimeDegreePackets.rootQuotientParametrization` and `OAI.PrimeDegreePackets.RootBox.domain` (definitions bundle `OAIQ244Duke022` of this split); `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.root_invariant_of_atomic_companion_leaves` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/LeafBoxSeparation.lean (declaration OAI.DukePrimeDegree.rootBox_leaf_separates_fibers_outside_nullset)

import Mathlib
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke022

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootBox_leaf_separates_fibers_outside_nullset
    (d : ℕ) {i j k : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ)
    (A : RootBox hij k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ z ∈ A.domain, ∀ w ∈ A.domain,
        rootQuotientParametrization hij z ∉ N →
        rootQuotientParametrization hij w ∉ N → z.1 = w.1 →
        intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) =
          intrinsicRootLeaf hij μ (rootQuotientParametrization hij w) → z = w := by
  sorry

end DukePrimeDegree

end

end OAI
end
