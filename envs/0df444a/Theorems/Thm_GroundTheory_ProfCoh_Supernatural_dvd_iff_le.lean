-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Supernatural_dvd_iff_le
-- name    : GroundTheory.ProfCoh.Supernatural.dvd_iff_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:03.477083+00:00
-- url     : https://prove2.me/theorems/00a540dd-e21f-4d80-8498-2e92c4962193
-- title:
--   Supernatural: dvd iff le
-- statement:
--   The Supernatural construction uses the dvd iff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L41-L50

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Supernatural

theorem GroundTheory.ProfCoh.Supernatural.dvd_iff_le {a b : Supernatural} : a ∣ b ↔ a ≤ b := by sorry
