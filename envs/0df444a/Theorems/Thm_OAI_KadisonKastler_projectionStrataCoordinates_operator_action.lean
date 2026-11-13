-- Prove2me | Theorems.Thm_OAI_KadisonKastler_projectionStrataCoordinates_operator_action
-- name    : OAI.KadisonKastler.projectionStrataCoordinates_operator_action
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T05:24:25.44513+00:00
-- url     : https://prove2.me/theorems/9cc8b0e9-1b31-4aa0-937f-b7f6f0560eb7
-- title:
--   OAI.KadisonKastler.projectionStrataCoordinates_operator_action: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.projectionStrataCoordinates_operator_action` of [lean/OAI/Analysis/KadisonKastler/ProjectionStratumFields.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ProjectionStratumFields.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open MeasureTheory`, `open scoped lp`):
--
--   ```lean
--   theorem projectionStrataCoordinates_operator_action
--       (T : E →L[ℂ] E) (R : X → H →L[ℂ] H)
--       (hRT : ∀ v : E, J (T v) =ᵐ[μ] fun x => R x (J v x)) (v : E) (n : ℕ) :
--       ∀ᵐ x : projectionRankStratum P b n ∂projectionStratumMeasure μ P b n,
--         projectionStrataCoordinates μ P hP b hb hPm hPn J hJ (T v) n x =
--           compressedStratumField P hP b hb R n x
--             (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v n x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.isometricExtension` (definitions bundle `OAIQ075A005` of this split); `OAI.KadisonKastler.ProjectionStrataSpace`, `OAI.KadisonKastler.projectionDimensionIndex`, `OAI.KadisonKastler.projectionRankStratum` and `OAI.KadisonKastler.projectionStratumMeasure` (definitions bundle `Q260K004` of this split); `OAI.KadisonKastler.compressedStratumField` (definitions bundle `Q260K019` of this split); `OAI.KadisonKastler.projectionStrataCoordinates` (definitions bundle `Q260K023` of this split).
--
--   **Used by.** The proofs of `OAI_KadisonKastler_commonRankCoordinates_action`, `OAI_KadisonKastler_commonRankOperatorField_action`, `OAI_KadisonKastler_commonRank_algebra_decompose`, `OAI.KadisonKastler.commonRank_algebra_decomposition` and `OAI.KadisonKastler.commonRank_field_mem_of_closure` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/ProjectionStratumFields.lean (declaration OAI.KadisonKastler.projectionStrataCoordinates_operator_action)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Nth
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Definitions.Def_Q260K023

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H]

attribute [local instance] OAI.KadisonKastler.compressedCoordinateMeasurable
local instance compressedCoordinateBorel_r0ba68b_1 (n : ℕ) : BorelSpace ℓ²(projectionDimensionIndex n, ℂ) := ⟨rfl⟩
local instance compressedCoordinateSeparable_r0ba68b_1 (n : ℕ) :
    TopologicalSpace.SeparableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  separable_scalarHilbertCoordinates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure X) (hPm : ∀ v, Measurable fun x => P x v) (hPn : ∀ x, ‖P x‖ ≤ 1)
  (J : E →ₗᵢ[ℂ] Lp H 2 μ)
  (hJ : ∀ f : Lp H 2 μ, KadisonSimilarity.isometricExtension J 1 f =ᵐ[μ]
    fun x => P x (f x))

theorem projectionStrataCoordinates_operator_action
    (T : E →L[ℂ] E) (R : X → H →L[ℂ] H)
    (hRT : ∀ v : E, J (T v) =ᵐ[μ] fun x => R x (J v x)) (v : E) (n : ℕ) :
    ∀ᵐ x : projectionRankStratum P b n ∂projectionStratumMeasure μ P b n,
      projectionStrataCoordinates μ P hP b hb hPm hPn J hJ (T v) n x =
        compressedStratumField P hP b hb R n x
          (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v n x) := by
  sorry

end

end KadisonKastler

end OAI
end
