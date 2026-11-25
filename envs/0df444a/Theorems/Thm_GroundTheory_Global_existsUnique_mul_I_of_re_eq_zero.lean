-- Prove2me | Theorems.Thm_GroundTheory_Global_existsUnique_mul_I_of_re_eq_zero
-- name    : GroundTheory.Global.existsUnique_mul_I_of_re_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:40:42.784301+00:00
-- url     : https://prove2.me/theorems/159f9309-ddcb-4126-82df-f8f321c97727
-- title:
--   Global: exists Unique mul I of re eq zero
-- statement:
--   The Global construction uses the exists Unique mul I of re eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnitary.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchCharsUnitary.lean#L14-L21

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

theorem GroundTheory.Global.existsUnique_mul_I_of_re_eq_zero {P : ℂ → Prop} (h : ∃! s, P s)
    (hre : ∀ s, P s → s.re = 0) : ∃! τ : ℝ, P ((τ : ℂ) * I) := by sorry
