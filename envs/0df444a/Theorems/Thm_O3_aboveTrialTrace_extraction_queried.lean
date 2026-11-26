-- Prove2me | Theorems.Thm_O3_aboveTrialTrace_extraction_queried
-- name    : O3.aboveTrialTrace_extraction_queried
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:57.492871+00:00
-- url     : https://prove2.me/theorems/fd30988e-f326-5360-9e4a-a4348302c738
-- title:
--   O3: above Trial Trace extraction queried
-- statement:
--   The O3 construction uses the above Trial Trace extraction queried property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L388-L397
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L388-L397

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveTrialTrace_extraction_queried {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d)
    (extraction : Vec d) :
    extraction ∈
      (aboveTrialTrace oracle horizons y accelerated extraction).map
        Observation.point := by sorry
