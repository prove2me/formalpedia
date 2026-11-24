-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_scaled_nontrivial_character
-- name    : GlobalTheory.T.exists_scaled_nontrivial_character
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:38:37.931401+00:00
-- url     : https://prove2.me/theorems/f05cb1a6-23c1-4db6-8abd-3c3b3a392e04
-- title:
--   T: exists scaled nontrivial character
-- statement:
--   The T construction uses the exists scaled nontrivial character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsScaledNontrivialCharacterStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsScaledNontrivialCharacterStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsScaledNontrivialCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsScaledNontrivialCharacterStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_scaled_nontrivial_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k), valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧ ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by sorry
