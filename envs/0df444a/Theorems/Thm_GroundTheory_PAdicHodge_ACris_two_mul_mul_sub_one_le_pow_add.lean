-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_two_mul_mul_sub_one_le_pow_add
-- name    : GroundTheory.PAdicHodge.ACris.two_mul_mul_sub_one_le_pow_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:21.767034+00:00
-- url     : https://prove2.me/theorems/89dd1e6b-7074-5cc7-9fe1-7522e00b3de2
-- title:
--   ACris: two mul mul sub one le pow add
-- statement:
--   The ACris construction uses the two mul mul sub one le pow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L25-L38

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

theorem GroundTheory.PAdicHodge.ACris.two_mul_mul_sub_one_le_pow_add (k : ℕ) : 2 * k * (p - 1) ≤ p ^ k + p := by sorry
