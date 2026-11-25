-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_real_of_even
-- name    : GroundTheory.Global.index_range_powMonoidHom_real_of_even
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:31.896466+00:00
-- url     : https://prove2.me/theorems/8b8daa25-aec0-49b1-9931-dff61eed6697
-- title:
--   Global: index range pow Monoid Hom real of even
-- statement:
--   The Global construction uses the index range pow Monoid Hom real of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L138-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L138-L146

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

theorem GroundTheory.Global.index_range_powMonoidHom_real_of_even {n : ℕ} (hn : n ≠ 0) (he : Even n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 2 := by sorry
