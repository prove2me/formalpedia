-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_zpow_sum_units
-- name    : GlobalTheory.CompanionTheory.StrictCone.zpow_sum_units
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:49.013722+00:00
-- url     : https://prove2.me/theorems/4937dc41-d996-478a-97c2-02413ddfd4dc
-- title:
--   Strict Cone: zpow sum units
-- statement:
--   The Strict Cone construction uses the zpow sum units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L71-L75

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativeCharacterOnCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StrictCone

theorem GlobalTheory.CompanionTheory.StrictCone.zpow_sum_units (Q : ℂˣ) {n : ℕ} (e : Fin n → ℤ) : Q ^ (∑ i, e i) = ∏ i, Q ^ e i := by sorry
