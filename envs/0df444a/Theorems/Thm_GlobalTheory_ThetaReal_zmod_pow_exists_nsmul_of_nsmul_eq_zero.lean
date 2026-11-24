-- Prove2me | Theorems.Thm_GlobalTheory_ThetaReal_zmod_pow_exists_nsmul_of_nsmul_eq_zero
-- name    : GlobalTheory.ThetaReal.zmod_pow_exists_nsmul_of_nsmul_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:07:43.633717+00:00
-- url     : https://prove2.me/theorems/bef98d57-d469-443e-9d97-eff455042659
-- title:
--   Theta Real: zmod pow exists nsmul of nsmul eq zero
-- statement:
--   The Theta Real construction uses the zmod pow exists nsmul of nsmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ClosureZmodPowEqTopOfMeetsTorsionCosets.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ClosureZmodPowEqTopOfMeetsTorsionCosets.lean#L5-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ClosureZmodPowEqTopOfMeetsTorsionCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ThetaReal

theorem GlobalTheory.ThetaReal.zmod_pow_exists_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : 1 ≤ n) (hJ : 2 ≤ J)
    (y : ZMod (n ^ J)) (hy : n • y = 0) : ∃ w : ZMod (n ^ J), y = n • w := by sorry
