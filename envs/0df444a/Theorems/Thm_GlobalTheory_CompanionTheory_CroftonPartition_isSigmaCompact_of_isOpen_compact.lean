-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CroftonPartition_isSigmaCompact_of_isOpen_compact
-- name    : GlobalTheory.CompanionTheory.CroftonPartition.isSigmaCompact_of_isOpen_compact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:06.613185+00:00
-- url     : https://prove2.me/theorems/fe52ba61-704a-4504-a270-7c4c76cdb204
-- title:
--   Crofton Partition: is Sigma Compact of is Open compact
-- statement:
--   The Crofton Partition construction uses the is Sigma Compact of is Open compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SigmaCompactDisjointRefinement.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SigmaCompactDisjointRefinement.lean#L9-L12

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

theorem GlobalTheory.CompanionTheory.CroftonPartition.isSigmaCompact_of_isOpen_compact {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] {U : Set X} (hU : IsOpen U) : IsSigmaCompact U := by sorry
