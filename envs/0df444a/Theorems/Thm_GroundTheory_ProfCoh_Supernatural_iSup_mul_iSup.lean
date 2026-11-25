-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Supernatural_iSup_mul_iSup
-- name    : GroundTheory.ProfCoh.Supernatural.iSup_mul_iSup
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:09.963195+00:00
-- url     : https://prove2.me/theorems/0ed252cf-d068-4834-b69d-5b858bcd8e92
-- title:
--   Supernatural: i Sup mul i Sup
-- statement:
--   The Supernatural construction uses the i Sup mul i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L107-L113

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

theorem GroundTheory.ProfCoh.Supernatural.iSup_mul_iSup {ι : Sort*} {f g : ι → Supernatural}
    (h : ∀ i j, ∃ k, f i ≤ f k ∧ g j ≤ g k) :
    (⨆ i, f i) * (⨆ i, g i) = ⨆ i, f i * g i := by sorry
