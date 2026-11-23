-- Prove2me | Theorems.Thm_GroundTheory_Global_normalizedAbv_apply
-- name    : GroundTheory.Global.normalizedAbv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:45.945347+00:00
-- url     : https://prove2.me/theorems/32b8db31-d479-438a-9722-cc7b5c2d29a9
-- title:
--   Global: normalized Abv apply
-- statement:
--   The Global construction uses the normalized Abv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L46-L47

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

theorem GroundTheory.Global.normalizedAbv_apply (x : v.adicCompletion K) : normalizedAbv v x = ‖x‖ := by sorry
