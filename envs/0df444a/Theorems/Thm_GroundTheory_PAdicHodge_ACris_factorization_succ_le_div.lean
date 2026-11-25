-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_factorization_succ_le_div
-- name    : GroundTheory.PAdicHodge.ACris.factorization_succ_le_div
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:15:02.943917+00:00
-- url     : https://prove2.me/theorems/e4520c13-e7bd-5d22-89d3-31d3e03bf62c
-- title:
--   ACris: factorization succ le div
-- statement:
--   The ACris construction uses the factorization succ le div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L40-L48

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

theorem GroundTheory.PAdicHodge.ACris.factorization_succ_le_div (n : ℕ) : (n + 1).factorization p ≤ n / (p - 1) := by sorry
