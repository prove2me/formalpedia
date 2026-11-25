-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_real
-- name    : GroundTheory.Global.index_range_powMonoidHom_real
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:31.601962+00:00
-- url     : https://prove2.me/theorems/626003ab-d3e4-4513-9830-1bb7e7bc454f
-- title:
--   Global: index range pow Monoid Hom real
-- statement:
--   The Global construction uses the index range pow Monoid Hom real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L152-L156

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

theorem GroundTheory.Global.index_range_powMonoidHom_real {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = if Even n then 2 else 1 := by sorry
