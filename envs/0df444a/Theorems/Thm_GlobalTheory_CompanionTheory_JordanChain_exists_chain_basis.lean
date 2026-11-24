-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_JordanChain_exists_chain_basis
-- name    : GlobalTheory.CompanionTheory.JordanChain.exists_chain_basis
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:47.864974+00:00
-- url     : https://prove2.me/theorems/43da785f-f71b-4c5c-bff3-9e4a4fa6033b
-- title:
--   Jordan Chain: exists chain basis
-- statement:
--   The Jordan Chain construction uses the exists chain basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsChainsOfRange.lean#L172-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsChainsOfRange.lean#L172-L178

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

theorem GlobalTheory.CompanionTheory.JordanChain.exists_chain_basis {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧
      LinearIndependent K (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1)) ∧
      span K (Set.range (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1))) = ⊤ := by sorry
