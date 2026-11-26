-- Prove2me | Theorems.Thm_O3_aboveTrialTrace_exact
-- name    : O3.aboveTrialTrace_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:44.9818+00:00
-- url     : https://prove2.me/theorems/086d63a3-2600-441f-9394-bd31594e9c76
-- title:
--   O3: above Trial Trace exact
-- statement:
--   The O3 construction uses the above Trial Trace exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L365-L377
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L365-L377

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveTrialTrace_exact {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d)
    (extraction : Vec d) :
    AboveObservationTraceExact oracle
      (aboveTrialTrace oracle horizons y accelerated extraction) := by sorry
