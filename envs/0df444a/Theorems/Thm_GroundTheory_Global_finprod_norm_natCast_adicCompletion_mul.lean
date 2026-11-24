-- Prove2me | Theorems.Thm_GroundTheory_Global_finprod_norm_natCast_adicCompletion_mul
-- name    : GroundTheory.Global.finprod_norm_natCast_adicCompletion_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:05.177727+00:00
-- url     : https://prove2.me/theorems/018828c9-f5c8-4176-acdb-fa2d52dcffc9
-- title:
--   Global: finprod norm nat Cast adic Completion mul
-- statement:
--   The Global construction uses the finprod norm nat Cast adic Completion mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexProductFormula.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexProductFormula.lean#L14-L24

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

theorem GroundTheory.Global.finprod_norm_natCast_adicCompletion_mul {n : ℕ} (hn : n ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(n : v.adicCompletion K)‖) *
      (n : ℝ) ^ Module.finrank ℚ K = 1 := by sorry
