-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_real_of_odd
-- name    : GroundTheory.Global.index_range_powMonoidHom_real_of_odd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:05.761702+00:00
-- url     : https://prove2.me/theorems/e4b63fd9-5f14-4924-af3f-9f572e5b1f77
-- title:
--   Global: index range pow Monoid Hom real of odd
-- statement:
--   The Global construction uses the index range pow Monoid Hom real of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L148-L150

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

theorem GroundTheory.Global.index_range_powMonoidHom_real_of_odd {n : ℕ} (ho : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 1 := by sorry
