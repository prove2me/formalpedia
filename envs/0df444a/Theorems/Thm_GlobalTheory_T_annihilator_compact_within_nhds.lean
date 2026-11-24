-- Prove2me | Theorems.Thm_GlobalTheory_T_annihilator_compact_within_nhds
-- name    : GlobalTheory.T.annihilator_compact_within_nhds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:11.338496+00:00
-- url     : https://prove2.me/theorems/8de57c00-06cf-4bb9-82f3-e7fcc81c8d4f
-- title:
--   T: annihilator compact within nhds
-- statement:
--   The T construction uses the annihilator compact within nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorCompactWithinNhdsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorCompactWithinNhdsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorCompactWithinNhds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorCompactWithinNhdsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.annihilator_compact_within_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (S : Set (Fin n → k)), S ∈ nhds (0 : Fin n → k) → ∃ Ξ : AddSubgroup (Fin n → k), IsCompact (Ξ : Set (Fin n → k)) ∧ ∀ t : Fin n → k, (∀ ξ ∈ Ξ, ψ (ξ ⬝ᵥ t) = 1) → t ∈ S := by sorry
