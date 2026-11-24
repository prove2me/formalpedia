-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CroftonPartition_exists_sigmaCompact_partition
-- name    : GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:20.034333+00:00
-- url     : https://prove2.me/theorems/0326347d-bbd8-4ec9-b3c2-6a7978469c07
-- title:
--   Crofton Partition: exists sigma Compact partition
-- statement:
--   The Crofton Partition construction uses the exists sigma Compact partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SigmaCompactDisjointRefinement.lean#L20-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SigmaCompactDisjointRefinement.lean#L20-L50

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SigmaCompactDisjointRefinement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CroftonPartition

theorem GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) →
    (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X),
      Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧
      ∀ t, IsSigmaCompact (A t) := by sorry
