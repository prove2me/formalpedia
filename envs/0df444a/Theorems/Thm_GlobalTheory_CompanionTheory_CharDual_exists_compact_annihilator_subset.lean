-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CharDual_exists_compact_annihilator_subset
-- name    : GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:12.541802+00:00
-- url     : https://prove2.me/theorems/5983901b-fa52-4580-947e-4635afe61d7f
-- title:
--   Char Dual: exists compact annihilator subset
-- statement:
--   The Char Dual construction uses the exists compact annihilator subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorCompactWithinNhds.lean#L7-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorCompactWithinNhds.lean#L7-L53

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorCompactWithinNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharDual

theorem GlobalTheory.CompanionTheory.CharDual.exists_compact_annihilator_subset : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (S : Set (Fin n → k)), S ∈ nhds (0 : Fin n → k) →
    ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧
      ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by sorry
