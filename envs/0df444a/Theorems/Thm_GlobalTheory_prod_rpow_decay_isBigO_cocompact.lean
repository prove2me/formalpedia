-- Prove2me | Theorems.Thm_GlobalTheory_prod_rpow_decay_isBigO_cocompact
-- name    : GlobalTheory.prod_rpow_decay_isBigO_cocompact
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:15:06.13586+00:00
-- url     : https://prove2.me/theorems/0ce9b669-d4d8-4eea-bb08-37391bf50b83
-- title:
--   Global Theory: prod rpow decay is Big O cocompact
-- statement:
--   The Global Theory construction uses the prod rpow decay is Big O cocompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdRpowDecayIsBigOCocompact.lean#L4-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdRpowDecayIsBigOCocompact.lean#L4-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdRpowDecayIsBigOCocompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory

theorem GlobalTheory.prod_rpow_decay_isBigO_cocompact : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by sorry
