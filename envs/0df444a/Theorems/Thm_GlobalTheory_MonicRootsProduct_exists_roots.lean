-- Prove2me | Theorems.Thm_GlobalTheory_MonicRootsProduct_exists_roots
-- name    : GlobalTheory.MonicRootsProduct.exists_roots
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:46:23.981971+00:00
-- url     : https://prove2.me/theorems/9bb263f1-626b-4634-bd25-c1d52d4765b5
-- title:
--   Monic Roots Product: exists roots
-- statement:
--   The Monic Roots Product construction uses the exists roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsProdXSubCOfMonic.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsProdXSubCOfMonic.lean#L19-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsProdXSubCOfMonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.MonicRootsProduct

theorem GlobalTheory.MonicRootsProduct.exists_roots {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ, ∏ j : Fin δ, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by sorry
