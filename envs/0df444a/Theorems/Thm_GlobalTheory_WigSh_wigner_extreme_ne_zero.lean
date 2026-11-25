-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_wigner_extreme_ne_zero
-- name    : GlobalTheory.WigSh.wigner_extreme_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:26.239659+00:00
-- url     : https://prove2.me/theorems/411093b1-b111-5489-b520-db909b823400
-- title:
--   Wig Sh: wigner extreme ne zero
-- statement:
--   The Wig Sh construction uses the wigner extreme ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WignerExtremeNeZero.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WignerExtremeNeZero.lean#L16-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WignerExtremeNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.WigSh

theorem GlobalTheory.WigSh.wigner_extreme_ne_zero : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (l : Fin (n+1)), StrictAnti L → ((∀ j, L j ≠ L l + 1) → GlobalTheory.WigSh.wP L (fun j : Fin n => L j.castSucc) l ≠ 0) ∧ ((∀ j, L j ≠ L l - 1) → GlobalTheory.WigSh.wM L (fun j : Fin n => L j.succ + 1) l ≠ 0) := by sorry
