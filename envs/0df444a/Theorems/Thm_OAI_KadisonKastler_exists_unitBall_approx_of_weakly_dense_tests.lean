-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_unitBall_approx_of_weakly_dense_tests
-- name    : OAI.KadisonKastler.exists_unitBall_approx_of_weakly_dense_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T08:55:50.017129+00:00
-- url     : https://prove2.me/theorems/a58d3df7-c669-4933-8425-869337b1fd39
-- title:
--   OAI.KadisonKastler.exists_unitBall_approx_of_weakly_dense_tests: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_unitBall_approx_of_weakly_dense_tests` of [lean/OAI/Analysis/KadisonKastler/DenseUnitBallGap.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/DenseUnitBallGap.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem exists_unitBall_approx_of_weakly_dense_tests
--       {ι : Type*} {M N : VonNeumannAlgebra H} (T : ι → H →L[ℂ] H)
--       (hT : WeakUnitBallDense T M) {r : ℝ} (hr : 0 ≤ r)
--       (hnear : ∀ i, ∃ b ∈ unitBall N, ‖T i - b‖ ≤ r)
--       (a : H →L[ℂ] H) (ha : a ∈ unitBall M) :
--       ∃ b ∈ unitBall N, ‖a - b‖ ≤ r
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonKastler.WeakUnitBallDense` (definitions bundle `Q260K013` of this split); `OAI.KadisonKastler.unitBall` (the published bundle `Def_StrongKadisonKastler`).
--
--   **Used by.** The proofs of `OAI.KadisonKastler.MatrixNearInclusion.spatialProduct` and `OAI.KadisonKastler.kkDistance_spatialProduct_le_of_matrixNearInclusion` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/DenseUnitBallGap.lean (declaration OAI.KadisonKastler.exists_unitBall_approx_of_weakly_dense_tests)

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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K013

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_unitBall_approx_of_weakly_dense_tests
    {ι : Type*} {M N : VonNeumannAlgebra H} (T : ι → H →L[ℂ] H)
    (hT : WeakUnitBallDense T M) {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ i, ∃ b ∈ unitBall N, ‖T i - b‖ ≤ r)
    (a : H →L[ℂ] H) (ha : a ∈ unitBall M) :
    ∃ b ∈ unitBall N, ‖a - b‖ ≤ r := by
  sorry

end

end KadisonKastler

end OAI
end
