-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Supernatural_le_def
-- name    : GroundTheory.ProfCoh.Supernatural.le_def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:56.058077+00:00
-- url     : https://prove2.me/theorems/d1bac418-9bf4-4d9e-a5f8-5b9b6917c935
-- title:
--   Supernatural: le def
-- statement:
--   The Supernatural construction uses the le def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L20-L20

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

theorem GroundTheory.ProfCoh.Supernatural.le_def {a b : Supernatural} : a ≤ b ↔ ∀ p, a.exp p ≤ b.exp p := by sorry
