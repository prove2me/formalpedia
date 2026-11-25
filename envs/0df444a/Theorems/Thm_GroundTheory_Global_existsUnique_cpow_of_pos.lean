-- Prove2me | Theorems.Thm_GroundTheory_Global_existsUnique_cpow_of_pos
-- name    : GroundTheory.Global.existsUnique_cpow_of_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:40:41.458263+00:00
-- url     : https://prove2.me/theorems/23af1859-2517-4fcf-9b72-1be619710f5a
-- title:
--   Global: exists Unique cpow of pos
-- statement:
--   The Global construction uses the exists Unique cpow of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnits.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnits.lean#L13-L27

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

theorem GroundTheory.Global.existsUnique_cpow_of_pos (χ : {x : ℝ // 0 < x} →ₜ* ℂˣ) :
    ∃! s : ℂ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ s := by sorry
