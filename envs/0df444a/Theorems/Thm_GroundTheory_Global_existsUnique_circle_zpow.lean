-- Prove2me | Theorems.Thm_GroundTheory_Global_existsUnique_circle_zpow
-- name    : GroundTheory.Global.existsUnique_circle_zpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:37.757177+00:00
-- url     : https://prove2.me/theorems/2a50598a-ab10-411d-a1f1-d825988325c7
-- title:
--   Global: exists Unique circle zpow
-- statement:
--   The Global construction uses the exists Unique circle zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnits.lean#L88-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnits.lean#L88-L117

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

theorem GroundTheory.Global.existsUnique_circle_zpow (χ : Circle →ₜ* ℂˣ) :
    ∃! m : ℤ, ∀ z : Circle, (χ z : ℂ) = (z : ℂ) ^ m := by sorry
