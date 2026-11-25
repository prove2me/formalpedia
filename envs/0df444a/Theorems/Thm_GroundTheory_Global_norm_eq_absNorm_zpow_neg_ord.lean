-- Prove2me | Theorems.Thm_GroundTheory_Global_norm_eq_absNorm_zpow_neg_ord
-- name    : GroundTheory.Global.norm_eq_absNorm_zpow_neg_ord
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:58.181231+00:00
-- url     : https://prove2.me/theorems/434d092f-fe6e-4cc1-a7d2-90f1f410ea9c
-- title:
--   Global: norm eq abs Norm zpow neg ord
-- statement:
--   The Global construction uses the norm eq abs Norm zpow neg ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L43-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L43-L71

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.norm_eq_absNorm_zpow_neg_ord {x : v.adicCompletion K} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ord x) := by sorry
