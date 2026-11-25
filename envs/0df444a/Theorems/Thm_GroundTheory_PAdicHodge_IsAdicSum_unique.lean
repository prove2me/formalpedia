-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsAdicSum_unique
-- name    : GroundTheory.PAdicHodge.IsAdicSum.unique
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:07:57.261263+00:00
-- url     : https://prove2.me/theorems/53f32572-7cc5-5711-91cb-017c02215a34
-- title:
--   Is Adic Sum: unique
-- statement:
--   The Is Adic Sum construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L24-L34

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

theorem GroundTheory.PAdicHodge.IsAdicSum.unique [IsHausdorff I R] {a : ℕ → R} {s s' : R} (hs : IsAdicSum I a s)
    (hs' : IsAdicSum I a s') : s = s' := by sorry
