-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsAdicSum_neg
-- name    : GroundTheory.PAdicHodge.IsAdicSum.neg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:08:56.018542+00:00
-- url     : https://prove2.me/theorems/2d3c2588-171e-5a8e-85b1-8cdeff0d1c97
-- title:
--   Is Adic Sum: neg
-- statement:
--   The Is Adic Sum construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L79-L81

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {I}

theorem GroundTheory.PAdicHodge.IsAdicSum.neg {a : ℕ → R} {s : R} (hs : IsAdicSum I a s) :
    IsAdicSum I (fun n => -a n) (-s) := by sorry
