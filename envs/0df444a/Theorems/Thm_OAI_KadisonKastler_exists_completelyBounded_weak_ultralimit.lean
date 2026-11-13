-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_completelyBounded_weak_ultralimit
-- name    : OAI.KadisonKastler.exists_completelyBounded_weak_ultralimit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T05:06:58.249608+00:00
-- url     : https://prove2.me/theorems/34b4b6d0-3f7b-4634-8847-4131b7f082e0
-- title:
--   OAI.KadisonKastler.exists_completelyBounded_weak_ultralimit: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_completelyBounded_weak_ultralimit` of [lean/OAI/Analysis/KadisonKastler/CompleteWeakLimits.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CompleteWeakLimits.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open Filter Generator`, `open scoped Topology InnerProductSpace`):
--
--   ```lean
--   theorem exists_completelyBounded_weak_ultralimit (M : VonNeumannAlgebra H)
--       {ι : Type*} (ω : Ultrafilter ι) (F : ι → Algebra M →ₗ[ℂ] Algebra M)
--       {c : ℝ} (hc : 0 ≤ c) (hF : ∀ i, CompletelyBoundedBy (F i) c) :
--       ∃ L : Algebra M →ₗ[ℂ] Algebra M, CompletelyBoundedBy L c ∧
--         ∀ a ξ η, Tendsto (fun i => inner ℂ η ((F i a : H →L[ℂ] H) ξ))
--           (ω : Filter ι) (𝓝 (inner ℂ η ((L a : H →L[ℂ] H) ξ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.vonNeumannToStarSubalgebraIsClosed` (definitions bundle `OAIQ075A002` of this split); `OAI.KadisonKastler.Algebra` and `OAI.KadisonKastler.algebraCStarAlgebra` (definitions bundle `Q260K002` of this split); `OAI.KadisonKastler.CompletelyBoundedBy` (definitions bundle `Q260K004` of this split); `OAI.KadisonKastler.completeWeakAlgebraOrder` and `OAI.KadisonKastler.completeWeakAlgebraStarOrder` (definitions bundle `Q260K014` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonKastler.constructedStabilityCoreInputs`, `OAI.KadisonKastler.exists_minimal_familyRowFamily`, `OAI_KadisonKastler_exists_simultaneous_modular_cluster`, `OAI.KadisonKastler.exists_universal_modular_rows`, `OAI_KadisonKastler_minimal_row_family_diagonal_norm`, `OAI.KadisonKastler.minimal_row_family_right_module_of_factorization`, `OAI.KadisonKastler.quadraticCochainSolver_of_modular_rows` and `OAI_KadisonKastler_quadratic_cochain_of_asymptotic_rows` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CompleteWeakLimits.lean (declaration OAI.KadisonKastler.exists_completelyBounded_weak_ultralimit)

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K014

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

noncomputable section

open Filter Generator
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.completeWeakOperatorOrder
local instance completeWeakOperatorStarOrder_r2c27b9_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
attribute [local instance] OAI.KadisonKastler.completeWeakAlgebraOrder
attribute [local instance] OAI.KadisonKastler.completeWeakAlgebraStarOrder
theorem exists_completelyBounded_weak_ultralimit (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (F : ι → Algebra M →ₗ[ℂ] Algebra M)
    {c : ℝ} (hc : 0 ≤ c) (hF : ∀ i, CompletelyBoundedBy (F i) c) :
    ∃ L : Algebra M →ₗ[ℂ] Algebra M, CompletelyBoundedBy L c ∧
      ∀ a ξ η, Tendsto (fun i => inner ℂ η ((F i a : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η ((L a : H →L[ℂ] H) ξ))) := by
  sorry

end

end KadisonKastler

end OAI
end
