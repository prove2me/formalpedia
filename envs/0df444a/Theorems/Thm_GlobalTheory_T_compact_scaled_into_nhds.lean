-- Prove2me | Theorems.Thm_GlobalTheory_T_compact_scaled_into_nhds
-- name    : GlobalTheory.T.compact_scaled_into_nhds
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:52.92248+00:00
-- url     : https://prove2.me/theorems/3bee63ae-d676-43e4-96ff-6e2156465fcc
-- title:
--   T: compact scaled into nhds
-- statement:
--   The T construction uses the compact scaled into nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompactScaledIntoNhdsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CompactScaledIntoNhdsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompactScaledIntoNhds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompactScaledIntoNhdsStatement
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

theorem GlobalTheory.T.compact_scaled_into_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∀ U ∈ nhds (0 : Fin n → k), ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ x ∈ K, ϖ ^ l • x ∈ U := by sorry
