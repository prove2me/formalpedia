-- Prove2me | Theorems.Thm_GroundTheory_Global_normalizedAbv_eq_toNNReal
-- name    : GroundTheory.Global.normalizedAbv_eq_toNNReal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:58.502227+00:00
-- url     : https://prove2.me/theorems/3d3d22ec-8907-4174-a3c4-c761b90f9062
-- title:
--   Global: normalized Abv eq to NNReal
-- statement:
--   The Global construction uses the normalized Abv eq to NNReal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L49-L51

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

theorem GroundTheory.Global.normalizedAbv_eq_toNNReal (x : v.adicCompletion K) :
    normalizedAbv v x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) := by sorry
