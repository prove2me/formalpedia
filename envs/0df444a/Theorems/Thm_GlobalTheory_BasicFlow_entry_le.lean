-- Prove2me | Theorems.Thm_GlobalTheory_BasicFlow_entry_le
-- name    : GlobalTheory.BasicFlow.entry_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:09.901965+00:00
-- url     : https://prove2.me/theorems/2371a11a-a496-439b-97d1-e5460f7d4c39
-- title:
--   Basic Flow: entry le
-- statement:
--   The Basic Flow construction uses the entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DropLevelsBasic.lean#L91-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DropLevelsBasic.lean#L91-L101

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.BasicFlow

theorem GlobalTheory.BasicFlow.entry_le (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d W x) (a : ZMod d) (i : ℕ) (hi : i ∈ oddLevels d) : x a i ≤ W a := by sorry
