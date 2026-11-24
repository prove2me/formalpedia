-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurableSet_meets_inter
-- name    : GlobalTheory.CompanionTheory.FSCrofton.measurableSet_meets_inter
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:48.553109+00:00
-- url     : https://prove2.me/theorems/813500c2-8d97-46a2-b0d3-d4675a8d0483
-- title:
--   FSCrofton: measurable Set meets inter
-- statement:
--   The FSCrofton construction uses the measurable Set meets inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L42-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L42-L74

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

theorem GlobalTheory.CompanionTheory.FSCrofton.measurableSet_meets_inter [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X]
    {A B : Set X} (hA : IsSigmaCompact A) (hB : IsOpen B) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) :
    MeasurableSet {C : Fin d → α → ℂ | ∃ z ∈ A ∩ B, ∀ k, ∑ j, C k j * b j z = 0} := by sorry
