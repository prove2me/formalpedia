-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_add_factorization_succ_le_div
-- name    : GroundTheory.PAdicHodge.ACris.add_factorization_succ_le_div
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:45.218946+00:00
-- url     : https://prove2.me/theorems/b5709ab3-5486-4749-99cf-902aa0f37fc8
-- title:
--   ACris: add factorization succ le div
-- statement:
--   The ACris construction uses the add factorization succ le div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L50-L61

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

theorem GroundTheory.PAdicHodge.ACris.add_factorization_succ_le_div {n j : ℕ} (hn : 2 * (p - 1) * j + 3 * p ≤ n) :
    j + (n + 1).factorization p ≤ n / (p - 1) := by sorry
