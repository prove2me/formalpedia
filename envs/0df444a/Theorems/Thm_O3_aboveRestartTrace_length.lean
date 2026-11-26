-- Prove2me | Theorems.Thm_O3_aboveRestartTrace_length
-- name    : O3.aboveRestartTrace_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:36.271086+00:00
-- url     : https://prove2.me/theorems/7e5b1a55-257d-4ecb-a0ac-872a968d7ede
-- title:
--   O3: above Restart Trace length
-- statement:
--   The O3 construction uses the above Restart Trace length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L350-L355
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L350-L355

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveRestartTrace_length {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d) :
    (aboveRestartTrace oracle horizons y accelerated).length =
      ((List.finRange S).map fun s => 2 * horizons s).sum := by sorry
