-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CroftonPartition_isSigmaCompact_inter_isClosed
-- name    : GlobalTheory.CompanionTheory.CroftonPartition.isSigmaCompact_inter_isClosed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:07.147668+00:00
-- url     : https://prove2.me/theorems/6803c61a-2d19-4e89-b00b-ff92c604522e
-- title:
--   Crofton Partition: is Sigma Compact inter is Closed
-- statement:
--   The Crofton Partition construction uses the is Sigma Compact inter is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SigmaCompactDisjointRefinement.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SigmaCompactDisjointRefinement.lean#L14-L18

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

theorem GlobalTheory.CompanionTheory.CroftonPartition.isSigmaCompact_inter_isClosed {X : Type} [TopologicalSpace X] {s C : Set X}
    (hs : IsSigmaCompact s) (hC : IsClosed C) : IsSigmaCompact (s ∩ C) := by sorry
