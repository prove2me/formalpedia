-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_natCast_le_encard_zeroSetIn_iff
-- name    : GlobalTheory.CompanionTheory.FSCrofton.natCast_le_encard_zeroSetIn_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:05.812802+00:00
-- url     : https://prove2.me/theorems/df4c422d-a278-4446-9e21-f74beed7b6e1
-- title:
--   FSCrofton: nat Cast le encard zero Set In iff
-- statement:
--   The FSCrofton construction uses the nat Cast le encard zero Set In iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L76-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeasurableZeroCount.lean#L76-L124

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

theorem GlobalTheory.CompanionTheory.FSCrofton.natCast_le_encard_zeroSetIn_iff [T2Space X] [SecondCountableTopology X] (A : Set X)
    (b : α → X → ℂ) (C : Fin d → α → ℂ) (N : ℕ) :
    (N : ℕ∞) ≤ (zeroSetIn A b C).encard ↔
      ∃ f : Fin N → countableBasis X,
        (∀ i j, i ≠ j → Disjoint (f i : Set X) (f j)) ∧
        ∀ i, ∃ z ∈ A ∩ (f i : Set X), ∀ k, ∑ j, C k j * b j z = 0 := by sorry
