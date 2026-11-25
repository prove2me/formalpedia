-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsAdicSum_mem
-- name    : GroundTheory.PAdicHodge.IsAdicSum.mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:23.28655+00:00
-- url     : https://prove2.me/theorems/e4187843-d7e9-435d-ac54-6496ab7d6a34
-- title:
--   Is Adic Sum: mem
-- statement:
--   The Is Adic Sum construction uses the mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L105-L109

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

theorem GroundTheory.PAdicHodge.IsAdicSum.mem {J : Ideal R} {k : ℕ} (hJ : I ^ k ≤ J) {a : ℕ → R} {s : R}
    (hs : IsAdicSum I a s) (ha : ∀ n, a n ∈ J) : s ∈ J := by sorry
