-- Prove2me | Theorems.Thm_O3_aboveRestartTrace_exact
-- name    : O3.aboveRestartTrace_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:08.364347+00:00
-- url     : https://prove2.me/theorems/aa0678dd-008e-5c01-a6ca-86420088e045
-- title:
--   O3: above Restart Trace exact
-- statement:
--   The O3 construction uses the above Restart Trace exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L340-L348
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L340-L348

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveRestartTrace_exact {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d) :
    AboveObservationTraceExact oracle
      (aboveRestartTrace oracle horizons y accelerated) := by sorry
