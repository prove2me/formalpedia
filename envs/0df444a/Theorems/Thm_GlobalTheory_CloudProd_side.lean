-- Prove2me | Theorems.Thm_GlobalTheory_CloudProd_side
-- name    : GlobalTheory.CloudProd.side
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:12.868101+00:00
-- url     : https://prove2.me/theorems/520f0724-a19e-4ca7-940f-7039baccc3da
-- title:
--   Cloud Prod: side
-- statement:
--   The Cloud Prod construction uses the side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SideSucc.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SideSucc.lean#L34-L42

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

theorem GlobalTheory.CloudProd.side (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range n, (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by sorry
