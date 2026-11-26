-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsAdicSum_sub
-- name    : GroundTheory.PAdicHodge.IsAdicSum.sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:10:22.446794+00:00
-- url     : https://prove2.me/theorems/d33da53d-7214-4ad8-88d4-32a1d4fe2317
-- title:
--   Is Adic Sum: sub
-- statement:
--   The Is Adic Sum construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L83-L85

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

theorem GroundTheory.PAdicHodge.IsAdicSum.sub {a b : ℕ → R} {s t : R} (hs : IsAdicSum I a s) (ht : IsAdicSum I b t) :
    IsAdicSum I (fun n => a n - b n) (s - t) := by sorry
