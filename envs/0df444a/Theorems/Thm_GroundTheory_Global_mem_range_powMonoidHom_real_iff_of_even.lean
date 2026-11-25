-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_range_powMonoidHom_real_iff_of_even
-- name    : GroundTheory.Global.mem_range_powMonoidHom_real_iff_of_even
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:29.372941+00:00
-- url     : https://prove2.me/theorems/4d9029a1-b3c8-4541-9fbf-508d3f166f52
-- title:
--   Global: mem range pow Monoid Hom real iff of even
-- statement:
--   The Global construction uses the mem range pow Monoid Hom real iff of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L110-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L110-L121

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

theorem GroundTheory.Global.mem_range_powMonoidHom_real_iff_of_even {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝˣ) :
    x ∈ (powMonoidHom n : ℝˣ →* ℝˣ).range ↔ 0 < (x : ℝ) := by sorry
