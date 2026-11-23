-- Prove2me | Theorems.Thm_GroundTheory_Global_normalizedAbv_eq_zpow
-- name    : GroundTheory.Global.normalizedAbv_eq_zpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:52.727803+00:00
-- url     : https://prove2.me/theorems/d81c025a-4569-4557-8ef3-1f7ff36c38f7
-- title:
--   Global: normalized Abv eq zpow
-- statement:
--   The Global construction uses the normalized Abv eq zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L53-L61

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.normalizedAbv_eq_zpow {x : v.adicCompletion K} (hx : x ≠ 0) :
    normalizedAbv v x = (Ideal.absNorm v.asIdeal : ℝ) ^ log (Valued.v x) := by sorry
