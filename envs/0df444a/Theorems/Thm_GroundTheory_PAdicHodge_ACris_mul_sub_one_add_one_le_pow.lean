-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_mul_sub_one_add_one_le_pow
-- name    : GroundTheory.PAdicHodge.ACris.mul_sub_one_add_one_le_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:22.812355+00:00
-- url     : https://prove2.me/theorems/d59aed9b-e6d5-4f28-8b33-f7dd8cc01597
-- title:
--   ACris: mul sub one add one le pow
-- statement:
--   The ACris construction uses the mul sub one add one le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L15-L23

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {p : ℕ} [hp : Fact p.Prime]

theorem GroundTheory.PAdicHodge.ACris.mul_sub_one_add_one_le_pow (k : ℕ) : k * (p - 1) + 1 ≤ p ^ k := by sorry
