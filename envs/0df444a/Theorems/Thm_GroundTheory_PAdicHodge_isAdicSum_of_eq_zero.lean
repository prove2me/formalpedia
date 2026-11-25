-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isAdicSum_of_eq_zero
-- name    : GroundTheory.PAdicHodge.isAdicSum_of_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:08:49.22382+00:00
-- url     : https://prove2.me/theorems/28c938a1-835d-4252-8ceb-610424d260f3
-- title:
--   PAdic Hodge: is Adic Sum of eq zero
-- statement:
--   The PAdic Hodge construction uses the is Adic Sum of eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L92-L96

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

theorem GroundTheory.PAdicHodge.isAdicSum_of_eq_zero {a : ℕ → R} {m : ℕ} (h : ∀ n, m ≤ n → a n = 0) :
    IsAdicSum I a (∑ n ∈ Finset.range m, a n) := by sorry
