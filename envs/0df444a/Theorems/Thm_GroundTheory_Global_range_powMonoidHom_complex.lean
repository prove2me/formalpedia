-- Prove2me | Theorems.Thm_GroundTheory_Global_range_powMonoidHom_complex
-- name    : GroundTheory.Global.range_powMonoidHom_complex
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:09.481582+00:00
-- url     : https://prove2.me/theorems/d66a5e68-660f-4d45-8b80-64bd61944998
-- title:
--   Global: range pow Monoid Hom complex
-- statement:
--   The Global construction uses the range pow Monoid Hom complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L158-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L158-L168

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

theorem GroundTheory.Global.range_powMonoidHom_complex {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range = ⊤ := by sorry
