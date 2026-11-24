-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CompactScaling_exists_pow_smul_mem
-- name    : GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:22.150774+00:00
-- url     : https://prove2.me/theorems/c5d7fc3a-2232-4748-8ea5-a1d0f19d9ffd
-- title:
--   Compact Scaling: exists pow smul mem
-- statement:
--   The Compact Scaling construction uses the exists pow smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompactScaledIntoNhds.lean#L8-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompactScaledIntoNhds.lean#L8-L25

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompactScaledIntoNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CompactScaling

theorem GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∀ U ∈ nhds (0 : Fin n → k), ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ x ∈ K, ϖ ^ l • x ∈ U := by sorry
