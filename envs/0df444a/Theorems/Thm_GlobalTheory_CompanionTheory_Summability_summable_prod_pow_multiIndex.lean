-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Summability_summable_prod_pow_multiIndex
-- name    : GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:33.788646+00:00
-- url     : https://prove2.me/theorems/07a8af0e-da83-4446-a5a1-58aa74896e6f
-- title:
--   Summability: summable prod pow multi Index
-- statement:
--   The Summability construction uses the summable prod pow multi Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableProdPowMultiIndex.lean#L5-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SummableProdPowMultiIndex.lean#L5-L27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableProdPowMultiIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Summability

theorem GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex : ∀ (r : ℕ) (x : Fin r → ℝ), (∀ i, 0 ≤ x i) → (∀ i, x i < 1) →
    Summable (fun j : Fin r → ℕ => ∏ i, x i ^ j i) := by sorry
