-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_isClosed_meets_compact
-- name    : GlobalTheory.CompanionTheory.FSCrofton.isClosed_meets_compact
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:14.963175+00:00
-- url     : https://prove2.me/theorems/068db954-d172-4e87-8907-4f3000e9c17b
-- title:
--   FSCrofton: is Closed meets compact
-- statement:
--   The FSCrofton construction uses the is Closed meets compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L16-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L16-L40

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCount
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
open TopologicalSpace
variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]

theorem GlobalTheory.CompanionTheory.FSCrofton.isClosed_meets_compact {K : Set X} (hK : IsCompact K) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) K) :
    IsClosed {C : Fin d → α → ℂ | ∃ z ∈ K, ∀ k, ∑ j, C k j * b j z = 0} := by sorry
