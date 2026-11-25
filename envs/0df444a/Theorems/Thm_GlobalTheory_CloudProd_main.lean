-- Prove2me | Theorems.Thm_GlobalTheory_CloudProd_main
-- name    : GlobalTheory.CloudProd.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:13:46.456891+00:00
-- url     : https://prove2.me/theorems/d242fa60-0d28-5ee6-a8f8-60432044be30
-- title:
--   Cloud Prod: main
-- statement:
--   The Cloud Prod construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SideSucc.lean#L44-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SideSucc.lean#L44-L91

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

theorem GlobalTheory.CloudProd.main : ∀ (k : ℕ) (c y : ℝ) (lam : ℕ → ℝ), 1 ≤ k → 1 ≤ c → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s - y| 1) ≤ ((2 + c) * (k : ℝ)) ^ 2 := by sorry
