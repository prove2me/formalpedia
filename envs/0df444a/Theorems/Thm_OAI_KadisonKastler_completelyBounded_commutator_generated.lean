-- Prove2me | Theorems.Thm_OAI_KadisonKastler_completelyBounded_commutator_generated
-- name    : OAI.KadisonKastler.completelyBounded_commutator_generated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T05:53:13.705008+00:00
-- url     : https://prove2.me/theorems/e00de7d1-eea2-4cbd-b01e-7e36b3b4504d
-- title:
--   OAI.KadisonKastler.completelyBounded_commutator_generated: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.completelyBounded_commutator_generated` of [lean/OAI/Analysis/KadisonKastler/AmplifiedCommutatorClosure.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/AmplifiedCommutatorClosure.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open Generator`, `open scoped BigOperators`):
--
--   ```lean
--   theorem completelyBounded_commutator_generated
--       (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
--       (hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e)
--       (n : ℕ) (b : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H)
--       (hb : b ∈ matrixVonNeumann (generatedVonNeumannAlgebra π.range)) (hbn : ‖b‖ ≤ 1) :
--       ‖diagonalOperator T * b - b * diagonalOperator T‖ ≤ e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.FiniteHilbert` (definitions bundle `OAIQ075A002` of this split); `OAI.Generator.diagonalOperator` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonKastler.generatedVonNeumannAlgebra` and `OAI.KadisonKastler.matrixVonNeumann` (definitions bundle `Q260K002` of this split); `OAI.KadisonKastler.CompletelyBoundedBy` and `OAI.KadisonKastler.innerDerivation` (definitions bundle `Q260K004` of this split).
--
--   **Used by.** The proof of `OAI.KadisonKastler.finiteFactor_commutant_approx_of_gap` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/AmplifiedCommutatorClosure.lean (declaration OAI.KadisonKastler.completelyBounded_commutator_generated)

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K002
import Definitions.Def_Q260K004

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem completelyBounded_commutator_generated
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e)
    (n : ℕ) (b : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H)
    (hb : b ∈ matrixVonNeumann (generatedVonNeumannAlgebra π.range)) (hbn : ‖b‖ ≤ 1) :
    ‖diagonalOperator T * b - b * diagonalOperator T‖ ≤ e := by
  sorry

end

end KadisonKastler

end OAI
end
