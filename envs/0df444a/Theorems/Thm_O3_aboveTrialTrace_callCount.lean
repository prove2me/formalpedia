-- Prove2me | Theorems.Thm_O3_aboveTrialTrace_callCount
-- name    : O3.aboveTrialTrace_callCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:49.41968+00:00
-- url     : https://prove2.me/theorems/d3600930-f2c5-5cc8-bb6b-52d4b68e4bcf
-- title:
--   O3: above Trial Trace call Count
-- statement:
--   Exact count: two calls per accelerated iteration and one extraction call.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L380-L386
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L380-L386

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveTrialTrace_callCount {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d)
    (extraction : Vec d) :
    (aboveTrialTrace oracle horizons y accelerated extraction).length =
      ((List.finRange S).map fun s => 2 * horizons s).sum + 1 := by sorry
