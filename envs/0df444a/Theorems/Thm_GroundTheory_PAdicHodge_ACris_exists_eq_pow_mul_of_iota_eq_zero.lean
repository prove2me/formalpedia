-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_exists_eq_pow_mul_of_iota_eq_zero
-- name    : GroundTheory.PAdicHodge.ACris.exists_eq_pow_mul_of_iota_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:20.379099+00:00
-- url     : https://prove2.me/theorems/091f7665-d13a-4e7f-9b1a-4614f39e50e8
-- title:
--   ACris: exists eq pow mul of iota eq zero
-- statement:
--   The ACris construction uses the exists eq pow mul of iota eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L67-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L67-L105

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
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
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
set_option maxHeartbeats 1600000

theorem GroundTheory.PAdicHodge.ACris.exists_eq_pow_mul_of_iota_eq_zero {y : ACris K p} (hy : iota K p y = 0) {k : ℕ}
    {yk : ACrisZero K p}
    (ha : y - _root_.AdicCompletion.of _ _ yk ∈
      (Ideal.span {(p : ACrisZero K p)} ^ k).map (algebraMap (ACrisZero K p) (ACris K p))) :
    ∃ z ∈ ACrisZero K p, (yk : 𝔸) = (p : 𝔸) ^ k * z := by sorry
