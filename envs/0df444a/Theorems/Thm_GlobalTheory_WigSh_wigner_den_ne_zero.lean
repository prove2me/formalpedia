-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_wigner_den_ne_zero
-- name    : GlobalTheory.WigSh.wigner_den_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:39:45.3378+00:00
-- url     : https://prove2.me/theorems/2ab29210-79e9-432a-92ed-e52b4e32145a
-- title:
--   Wig Sh: wigner den ne zero
-- statement:
--   The Wig Sh construction uses the wigner den ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WignerExtremeNeZero.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WignerExtremeNeZero.lean#L8-L14

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

theorem GlobalTheory.WigSh.wigner_den_ne_zero {n : ℕ} (L : Fin (n+1) → ℤ) (l : Fin (n+1)) (hL : StrictAnti L) :
    (∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))) ≠ 0 := by sorry
