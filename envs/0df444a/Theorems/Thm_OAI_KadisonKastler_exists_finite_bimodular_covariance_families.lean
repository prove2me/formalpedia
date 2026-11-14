-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_finite_bimodular_covariance_families
-- name    : OAI.KadisonKastler.exists_finite_bimodular_covariance_families
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T05:06:23.100148+00:00
-- url     : https://prove2.me/theorems/0629da4b-bc39-4733-9532-67ea4afa630e
-- title:
--   OAI.KadisonKastler.exists_finite_bimodular_covariance_families: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_finite_bimodular_covariance_families` of [lean/OAI/Analysis/KadisonKastler/FiniteBimodularBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/FiniteBimodularBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`):
--
--   ```lean
--   theorem exists_finite_bimodular_covariance_families
--       (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
--       (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
--       (φ : R →⋆ₐ[ℂ] Algebra M)
--       (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
--         ∃ c : ℂ, b = c • (1 : Algebra M))
--       (V : E →L[ℂ] E) (L Q : unitary R → unitary (E →L[ℂ] E))
--       (hL : ∀ (u : unitary R) (x : Algebra M), J (φ u * x) = (L u : E →L[ℂ] E) (J x))
--       (hQ : ∀ (u : unitary R) (x : Algebra M), J (x * φ u) = (Q u : E →L[ℂ] E) (J x))
--       (hVL : ∀ u, Commute V (L u : E →L[ℂ] E))
--       (hVQ : ∀ u, Commute V (Q u : E →L[ℂ] E))
--       (a b : Algebra M) (ha : traceTwoNorm τ a ≤ 1) (hb : traceTwoNorm τ b ≤ 1) :
--       ∃ n : ℕ, 0 < n ∧ ∃ f g : Fin n → Algebra M,
--         (∀ i, traceTwoNorm τ (f i) ≤ 1) ∧
--         (∀ i, traceTwoNorm τ (g i) ≤ 1) ∧
--         traceTwoNorm τ (finiteSignRightCovariance f) ≤ 2 ∧
--         traceTwoNorm τ (finiteSignLeftCovariance f) ≤ 2 ∧
--         traceTwoNorm τ (finiteSignRightCovariance g) ≤ 2 ∧
--         traceTwoNorm τ (finiteSignLeftCovariance g) ≤ 2 ∧
--         (∀ i, inner ℂ (V (J (f i))) (J (g i)) = inner ℂ (V (J a)) (J b))
--   ```
--
--   **Definitions.** The statement is written with `OAI.vonNeumannToStarSubalgebraIsClosed` (definitions bundle `OAIQ075A002` of this split); `OAI.KadisonKastler.Algebra`, `OAI.KadisonKastler.FaithfulTracialState`, `OAI.KadisonKastler.algebraCStarAlgebra` and `OAI.KadisonKastler.traceTwoNorm` (definitions bundle `Q260K002` of this split); `OAI.KadisonKastler.finiteSignLeftCovariance` and `OAI.KadisonKastler.finiteSignRightCovariance` (definitions bundle `Q260K007` of this split); `OAI.KadisonKastler.FiniteVectorTrace` (definitions bundle `Q260K012` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonKastler.CommonTracialPositionData.conjugations_sub_le` and `OAI_KadisonKastler_CommonTracialPositionData_exists_finiteFactor_isomorphism` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/FiniteBimodularBound.lean (declaration OAI.KadisonKastler.exists_finite_bimodular_covariance_families)

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K007
import Definitions.Def_Q260K012

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

noncomputable section

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [CStarAlgebra R] {M : VonNeumannAlgebra H}

theorem exists_finite_bimodular_covariance_families
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (V : E →L[ℂ] E) (L Q : unitary R → unitary (E →L[ℂ] E))
    (hL : ∀ (u : unitary R) (x : Algebra M), J (φ u * x) = (L u : E →L[ℂ] E) (J x))
    (hQ : ∀ (u : unitary R) (x : Algebra M), J (x * φ u) = (Q u : E →L[ℂ] E) (J x))
    (hVL : ∀ u, Commute V (L u : E →L[ℂ] E))
    (hVQ : ∀ u, Commute V (Q u : E →L[ℂ] E))
    (a b : Algebra M) (ha : traceTwoNorm τ a ≤ 1) (hb : traceTwoNorm τ b ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ f g : Fin n → Algebra M,
      (∀ i, traceTwoNorm τ (f i) ≤ 1) ∧
      (∀ i, traceTwoNorm τ (g i) ≤ 1) ∧
      traceTwoNorm τ (finiteSignRightCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignRightCovariance g) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance g) ≤ 2 ∧
      (∀ i, inner ℂ (V (J (f i))) (J (g i)) = inner ℂ (V (J a)) (J b)) := by
  sorry

end

end KadisonKastler

end OAI
end
