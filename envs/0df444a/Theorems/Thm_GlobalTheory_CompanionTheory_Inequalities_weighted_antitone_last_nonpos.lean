-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Inequalities_weighted_antitone_last_nonpos
-- name    : GlobalTheory.CompanionTheory.Inequalities.weighted_antitone_last_nonpos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:11:12.77679+00:00
-- url     : https://prove2.me/theorems/75be4e42-ac1a-4978-848f-9c70a70d290e
-- title:
--   Inequalities: weighted antitone last nonpos
-- statement:
--   The Inequalities construction uses the weighted antitone last nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WeightedAntitoneLastNonpos.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WeightedAntitoneLastNonpos.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WeightedAntitoneLastNonpos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Inequalities

theorem GlobalTheory.CompanionTheory.Inequalities.weighted_antitone_last_nonpos : ∀ (h : ℕ) (d e : Fin h → ℝ), 2 ≤ h → (∀ i, 0 < d i) →
    Antitone e → ∑ i, d i * e i = 0 →
    ∃ j : Fin h, 0 < j.val ∧ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i ≤ 0 := by sorry
