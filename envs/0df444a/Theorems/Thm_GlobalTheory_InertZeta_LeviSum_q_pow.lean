-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_LeviSum_q_pow
-- name    : GlobalTheory.InertZeta.LeviSum.q_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:45.576446+00:00
-- url     : https://prove2.me/theorems/d927b8e6-b307-4a9d-8af9-d1499f5f3574
-- title:
--   Levi Sum: q pow
-- statement:
--   The Levi Sum construction uses the q pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryLeviSummationGeometricSeries.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryLeviSummationGeometricSeries.lean#L23-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryLeviSummationGeometricSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.LeviSum

theorem GlobalTheory.InertZeta.LeviSum.q_pow (q : ℂ) (hq : q ≠ 0) (N : ℕ) (a : ℤ) :
    q ^ ((2 * N + 2) * a.toNat) * q ^ (-a * ((N : ℤ) + 1)) = (q ^ (N + 1)) ^ a.natAbs := by sorry
