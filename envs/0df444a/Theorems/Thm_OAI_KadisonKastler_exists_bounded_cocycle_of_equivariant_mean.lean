-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_bounded_cocycle_of_equivariant_mean
-- name    : OAI.KadisonKastler.exists_bounded_cocycle_of_equivariant_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T05:11:48.137904+00:00
-- url     : https://prove2.me/theorems/05be0a32-afe6-4b36-944b-f7052bea8a33
-- title:
--   OAI.KadisonKastler.exists_bounded_cocycle_of_equivariant_mean: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_bounded_cocycle_of_equivariant_mean` of [lean/OAI/Analysis/KadisonKastler/BoundaryBoundedTransport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/BoundaryBoundedTransport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open scoped BoundedContinuousFunction CStarAlgebra`):
--
--   ```lean
--   theorem exists_bounded_cocycle_of_equivariant_mean
--       (α : G →* (B ≃⋆ₐ[ℂ] B))
--       (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
--       (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
--       (V : unitary (G →ᵇ B)) (hV : unitaryCocycleDefect α V ≤ 1 / 64) :
--       ∃ W : unitary (G →ᵇ B),
--         (∀ g h, W.val g * α g (W.val h) = W.val (g * h)) ∧
--         dist V W ≤ 2 * unitaryCocycleDefect α V
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonKastler.boundaryConstant` (definitions bundle `Q260K003` of this split); `OAI.KadisonKastler.BimoduleMean` and `OAI.KadisonKastler.boundaryTranslate` (definitions bundle `Q260K004` of this split); `OAI.KadisonKastler.boundaryBoundedCStar` (definitions bundle `Q260K005` of this split); `OAI.KadisonKastler.unitaryCocycleDefect` (definitions bundle `Q260K015` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonKastler.ScalarBoundaryMean.exists_measurable_cocycle_near_representation`, `OAI.KadisonKastler.exists_group_representation_of_mean`, `OAI_KadisonKastler_exists_standard_finiteFactor_isomorphism` and `OAI.KadisonKastler.exists_unitary_finiteMatrix_embedding` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/BoundaryBoundedTransport.lean (declaration OAI.KadisonKastler.exists_bounded_cocycle_of_equivariant_mean)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Q260K015

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

attribute [local instance] OAI.KadisonKastler.boundaryBoundedCStar
theorem exists_bounded_cocycle_of_equivariant_mean
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (V : unitary (G →ᵇ B)) (hV : unitaryCocycleDefect α V ≤ 1 / 64) :
    ∃ W : unitary (G →ᵇ B),
      (∀ g h, W.val g * α g (W.val h) = W.val (g * h)) ∧
      dist V W ≤ 2 * unitaryCocycleDefect α V := by
  sorry

end

end KadisonKastler

end OAI
end
