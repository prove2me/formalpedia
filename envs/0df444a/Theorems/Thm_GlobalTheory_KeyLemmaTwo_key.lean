-- Prove2me | Theorems.Thm_GlobalTheory_KeyLemmaTwo_key
-- name    : GlobalTheory.KeyLemmaTwo.key
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:01.032518+00:00
-- url     : https://prove2.me/theorems/b53807c1-5a08-4b94-92f3-6abb71d974e0
-- title:
--   Key Lemma Two: key
-- statement:
--   The Key Lemma Two construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ImportsAlt.lean#L5-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ImportsAlt.lean#L5-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KeyLemmaTwo

theorem GlobalTheory.KeyLemmaTwo.key {z : ℂ} (h : ∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by sorry
