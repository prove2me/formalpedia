-- Prove2me | Theorems.Thm_O3_abovePhaseTrace_length
-- name    : O3.abovePhaseTrace_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:26.798406+00:00
-- url     : https://prove2.me/theorems/f40dc7b1-439e-47cf-8c38-b73a28133417
-- title:
--   O3: above Phase Trace length
-- statement:
--   The O3 construction uses the above Phase Trace length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L323-L327
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L323-L327

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.abovePhaseTrace_length {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) :
    (abovePhaseTrace oracle y accelerated).length = 2 * N := by sorry
