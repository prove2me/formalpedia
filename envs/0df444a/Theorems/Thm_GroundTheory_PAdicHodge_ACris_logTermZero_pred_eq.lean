-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_logTermZero_pred_eq
-- name    : GroundTheory.PAdicHodge.ACris.logTermZero_pred_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:35.365927+00:00
-- url     : https://prove2.me/theorems/2e491de4-ff9f-5de3-b8b3-a203c3c760a2
-- title:
--   ACris: log Term Zero pred eq
-- statement:
--   The ACris construction uses the log Term Zero pred eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L299-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L299-L316

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

theorem GroundTheory.PAdicHodge.ACris.logTermZero_pred_eq {x : AInf K p} (hx : x ∈ RingHom.ker θ) {c : ACrisZero K p}
    (hc : (algebraMap (AInf K p) (ACrisZero K p) x) ^ (p - 1) = (p : ACrisZero K p) * c) :
    logTermZero hx (p - 1) = algebraMap (AInf K p) (ACrisZero K p) x * ((-1) ^ (p - 1) * c) := by sorry
