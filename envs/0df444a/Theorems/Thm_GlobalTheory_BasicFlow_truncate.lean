-- Prove2me | Theorems.Thm_GlobalTheory_BasicFlow_truncate
-- name    : GlobalTheory.BasicFlow.truncate
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:47.330228+00:00
-- url     : https://prove2.me/theorems/6d9735e9-50b2-4906-abfb-374b5acde530
-- title:
--   Basic Flow: truncate
-- statement:
--   The Basic Flow construction uses the truncate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DropLevelsBasic.lean#L133-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DropLevelsBasic.lean#L133-L170

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

theorem GlobalTheory.BasicFlow.truncate (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (i0 : ℕ)
    (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d W x) :
    ∃ x' : ZMod d → ℕ → ℝ, IsFlow l d W x' ∧
      (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x' a i = 0) ∧
      flowVal d x ≤ flowVal d x' + (∑ a, W a) / (l : ℝ) ^ i0 := by sorry
