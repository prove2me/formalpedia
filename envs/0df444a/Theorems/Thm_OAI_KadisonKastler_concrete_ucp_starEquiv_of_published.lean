-- Prove2me | Theorems.Thm_OAI_KadisonKastler_concrete_ucp_starEquiv_of_published
-- name    : OAI.KadisonKastler.concrete_ucp_starEquiv_of_published
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T05:06:50.127204+00:00
-- url     : https://prove2.me/theorems/b2977bfa-6f82-437b-a4cb-50b1a66577ae
-- title:
--   OAI.KadisonKastler.concrete_ucp_starEquiv_of_published: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.concrete_ucp_starEquiv_of_published` of [lean/OAI/Analysis/KadisonKastler/ConcreteUCP.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ConcreteUCP.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open scoped CStarAlgebra`):
--
--   ```lean
--   theorem concrete_ucp_starEquiv_of_published {M N : VonNeumannAlgebra H}
--       (hPublished : PublishedMultiplicationCorrection M)
--       (φ : Algebra M →CP Algebra N) (hφ : φ 1 = 1)
--       {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) (hge : g + e < 1)
--       (hclose : CompletelyBoundedBy
--         ((algebraInclusion N).toAlgHom.toLinearMap.comp φ.toLinearMap -
--           (algebraInclusion M).toAlgHom.toLinearMap) e)
--       (hgap : kkDistance M N < g) :
--       ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
--         CompletelyBoundedBy
--           ((algebraInclusion N).toAlgHom.toLinearMap.comp θ.toAlgEquiv.toLinearMap -
--             (algebraInclusion M).toAlgHom.toLinearMap) (32 * e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.vonNeumannToStarSubalgebraIsClosed` (definitions bundle `OAIQ075A002` of this split); `OAI.KadisonKastler.Algebra` and `OAI.KadisonKastler.algebraCStarAlgebra` (definitions bundle `Q260K002` of this split); `OAI.KadisonKastler.CompletelyBoundedBy` (definitions bundle `Q260K004` of this split); `OAI.KadisonKastler.instPartialOrderContinuousLinearMapComplexId_solutions_1` and `OAI.KadisonKastler.instStarOrderedRingContinuousLinearMapComplexId_solutions_1` (definitions bundle `Q260K007` of this split); `OAI.KadisonKastler.PublishedMultiplicationCorrection` (definitions bundle `Q260K012` of this split); `OAI.KadisonKastler.algebraInclusion` (definitions bundle `Q260K013` of this split); `OAI.KadisonKastler.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2` and `OAI.KadisonKastler.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2` (definitions bundle `Q260K015` of this split); `OAI.KadisonKastler.kkDistance` (the published bundle `Def_StrongKadisonKastler`).
--
--   **Used by.** The proof of `OAI.KadisonKastler.concrete_ucp_unitary_of_published` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ConcreteUCP.lean (declaration OAI.KadisonKastler.concrete_ucp_starEquiv_of_published)

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K012
import Definitions.Def_Q260K013
import Definitions.Def_Q260K015

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.instPartialOrderContinuousLinearMapComplexId_solutions_1
attribute [local instance] OAI.KadisonKastler.instStarOrderedRingContinuousLinearMapComplexId_solutions_1
attribute [local instance] OAI.KadisonKastler.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2
attribute [local instance] OAI.KadisonKastler.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2
theorem concrete_ucp_starEquiv_of_published {M N : VonNeumannAlgebra H}
    (hPublished : PublishedMultiplicationCorrection M)
    (φ : Algebra M →CP Algebra N) (hφ : φ 1 = 1)
    {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) (hge : g + e < 1)
    (hclose : CompletelyBoundedBy
      ((algebraInclusion N).toAlgHom.toLinearMap.comp φ.toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap) e)
    (hgap : kkDistance M N < g) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      CompletelyBoundedBy
        ((algebraInclusion N).toAlgHom.toLinearMap.comp θ.toAlgEquiv.toLinearMap -
          (algebraInclusion M).toAlgHom.toLinearMap) (32 * e) := by
  sorry

end

end KadisonKastler

end OAI
end
