-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Tempered_weighted_antitone_eq_zero_of_tails_nonneg
-- name    : GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:28.288321+00:00
-- url     : https://prove2.me/theorems/b16efd4e-c929-40b2-ba94-7f168e56e528
-- title:
--   Tempered: weighted antitone eq zero of tails nonneg
-- statement:
--   The Tempered construction uses the weighted antitone eq zero of tails nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AntitoneWeightedSumZero.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AntitoneWeightedSumZero.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AntitoneWeightedSumZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Tempered

theorem GlobalTheory.CompanionTheory.Tempered.weighted_antitone_eq_zero_of_tails_nonneg :
    ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 →
      (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) →
      ∀ i, e i = 0 := by sorry
