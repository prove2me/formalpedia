-- Prove2me | Theorems.Thm_GroundTheory_Global_circle_coe_zpow
-- name    : GroundTheory.Global.circle_coe_zpow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:11.376174+00:00
-- url     : https://prove2.me/theorems/5be31f58-49b0-40d6-a352-643c54835ea5
-- title:
--   Global: circle coe zpow
-- statement:
--   The Global construction uses the circle coe zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnitary.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnitary.lean#L73-L74

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
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
open Complex

theorem GroundTheory.Global.circle_coe_zpow (z : Circle) (m : ℤ) : ((z ^ m : Circle) : ℂ) = (z : ℂ) ^ m := by sorry
