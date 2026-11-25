-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_log_pow_mem
-- name    : GroundTheory.PAdicHodge.ACris.log_pow_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:34.240839+00:00
-- url     : https://prove2.me/theorems/c0721e0d-d496-42a4-a216-7a2ee3b7d629
-- title:
--   ACris: log pow mem
-- statement:
--   The ACris construction uses the log pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L320-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L320-L377

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
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
set_option maxHeartbeats 2000000

theorem GroundTheory.PAdicHodge.ACris.log_pow_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) {c : ACrisZero K p}
    (hc : (algebraMap (AInf K p) (ACrisZero K p) x) ^ (p - 1) = (p : ACrisZero K p) * c) :
    log hx ^ (p - 1) ∈ 𝔭 := by sorry
