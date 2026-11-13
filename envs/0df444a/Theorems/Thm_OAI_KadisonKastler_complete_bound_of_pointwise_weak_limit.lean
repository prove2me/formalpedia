-- Prove2me | Theorems.Thm_OAI_KadisonKastler_complete_bound_of_pointwise_weak_limit
-- name    : OAI.KadisonKastler.complete_bound_of_pointwise_weak_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:47:31.675547+00:00
-- url     : https://prove2.me/theorems/1ebe876b-5b3b-41cc-8b33-c5251930af10
-- title:
--   OAI.KadisonKastler.complete_bound_of_pointwise_weak_limit: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.complete_bound_of_pointwise_weak_limit` of [lean/OAI/Analysis/KadisonKastler/WeakCPLimits.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/WeakCPLimits.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open Filter`, `open scoped Topology CStarAlgebra`):
--
--   ```lean
--   theorem complete_bound_of_pointwise_weak_limit
--       (F : ι → A →ₗ[ℂ] (H →L[ℂ] H)) (S ρ : A →ₗ[ℂ] (H →L[ℂ] H))
--       (ht : ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) l
--         (𝓝 (inner ℂ y (S a x))))
--       {e : ℝ} (he : 0 ≤ e) (hF : ∀ i, CompletelyBoundedBy (F i - ρ) e) :
--       CompletelyBoundedBy (S - ρ) e
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonKastler.CompletelyBoundedBy` (definitions bundle `Q260K004` of this split).
--
--   **Used by.** The proofs of `OAI_KadisonKastler_concrete_unitary_of_finite_coefficient_tests`, `OAI.KadisonKastler.exists_normalizer_of_smoothed_approximation` and `OAI.KadisonKastler.universalStrongStability_of_separable` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/WeakCPLimits.lean (declaration OAI.KadisonKastler.complete_bound_of_pointwise_weak_limit)

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K004

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} [l.NeBot]

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem complete_bound_of_pointwise_weak_limit
    (F : ι → A →ₗ[ℂ] (H →L[ℂ] H)) (S ρ : A →ₗ[ℂ] (H →L[ℂ] H))
    (ht : ∀ a x y, Tendsto (fun i => inner ℂ y (F i a x)) l
      (𝓝 (inner ℂ y (S a x))))
    {e : ℝ} (he : 0 ≤ e) (hF : ∀ i, CompletelyBoundedBy (F i - ρ) e) :
    CompletelyBoundedBy (S - ρ) e := by
  sorry

end

end KadisonKastler

end OAI
end
