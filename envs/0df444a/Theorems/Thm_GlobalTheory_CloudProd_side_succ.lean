-- Prove2me | Theorems.Thm_GlobalTheory_CloudProd_side_succ
-- name    : GlobalTheory.CloudProd.side_succ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:03.383804+00:00
-- url     : https://prove2.me/theorems/afbebcf3-b5d9-4bbf-a819-5024b974bf0a
-- title:
--   Cloud Prod: side succ
-- statement:
--   The Cloud Prod construction uses the side succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SideSucc.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SideSucc.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SideSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CloudProd

theorem GlobalTheory.CloudProd.side_succ (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n + 1 → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range (n + 1), (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by sorry
