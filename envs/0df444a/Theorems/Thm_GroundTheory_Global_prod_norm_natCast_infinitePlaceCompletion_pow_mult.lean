-- Prove2me | Theorems.Thm_GroundTheory_Global_prod_norm_natCast_infinitePlaceCompletion_pow_mult
-- name    : GroundTheory.Global.prod_norm_natCast_infinitePlaceCompletion_pow_mult
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:26.67098+00:00
-- url     : https://prove2.me/theorems/05b481ca-5126-4cd1-a81a-917516eb61c1
-- title:
--   Global: prod norm nat Cast infinite Place Completion pow mult
-- statement:
--   The Global construction uses the prod norm nat Cast infinite Place Completion pow mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexProductFormula.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexProductFormula.lean#L35-L43

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.prod_norm_natCast_infinitePlaceCompletion_pow_mult (n : ℕ) :
    ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = (n : ℝ) ^ Module.finrank ℚ K := by sorry
