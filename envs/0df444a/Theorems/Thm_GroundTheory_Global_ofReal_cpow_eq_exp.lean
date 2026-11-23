-- Prove2me | Theorems.Thm_GroundTheory_Global_ofReal_cpow_eq_exp
-- name    : GroundTheory.Global.ofReal_cpow_eq_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:29.366543+00:00
-- url     : https://prove2.me/theorems/1b7d020e-bb4e-4adb-b410-b24284408c28
-- title:
--   Global: of Real cpow eq exp
-- statement:
--   The Global construction uses the of Real cpow eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnits.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnits.lean#L8-L11

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
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

theorem GroundTheory.Global.ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (u : ℂ) :
    (r : ℂ) ^ u = Complex.exp (u * (Real.log r : ℝ)) := by sorry
