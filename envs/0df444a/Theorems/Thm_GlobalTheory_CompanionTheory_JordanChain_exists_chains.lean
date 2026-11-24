-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_JordanChain_exists_chains
-- name    : GlobalTheory.CompanionTheory.JordanChain.exists_chains
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:58.933153+00:00
-- url     : https://prove2.me/theorems/e6925f2f-d5bb-464a-b923-be1b05b03d29
-- title:
--   Jordan Chain: exists chains
-- statement:
--   The Jordan Chain construction uses the exists chains property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsChainsOfRange.lean#L135-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsChainsOfRange.lean#L135-L170

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsChainsOfRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.JordanChain
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.CompanionTheory.JordanChain.exists_chains : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V), finrank K V = n → IsNilpotent f →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by sorry
