-- Prove2me | Theorems.Thm_NLDefined_theorem_iff_valid
-- name    : NLDefined.theorem_iff_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T19:18:25.448818+00:00
-- url     : https://prove2.me/theorems/0c95a638-fee9-489d-8647-ba5e3437e81e
-- title:
--   NLDefined: theorem iff valid
-- statement:
--   The NLDefined construction uses the theorem iff valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L195-L196
-- source:
--   https://github.com/thiagovscoelho/NelsonNL/blob/b0642ff38cde226f467eeb64eba780b94dd3100a/NLDefined.lean#L195-L196

import Std
import Definitions.Def_NLDefined
set_option autoImplicit true
set_option autoImplicit false
open NLDefined

theorem NLDefined.theorem_iff_valid (a : Formula) : Theorem a ↔ Valid a := by sorry
