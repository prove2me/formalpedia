-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CharConductor_exists_conductor_step
-- name    : GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:15.785082+00:00
-- url     : https://prove2.me/theorems/7394180c-8625-46ba-bbc8-e39b9ac4ce5d
-- title:
--   Char Conductor: exists conductor step
-- statement:
--   The Char Conductor construction uses the exists conductor step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsScaledNontrivialCharacter.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsScaledNontrivialCharacter.lean#L8-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsScaledNontrivialCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharConductor

theorem GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k),
    valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧
      ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by sorry
