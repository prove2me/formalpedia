-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_theta_logTerm
-- name    : GroundTheory.PAdicHodge.ACris.theta_logTerm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:08:48.110335+00:00
-- url     : https://prove2.me/theorems/2ac43df7-98e7-5af6-bb1d-71100c24ab6d
-- title:
--   ACris: theta log Term
-- statement:
--   The ACris construction uses the theta log Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L197-L200

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
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
variable [CharZero K]

theorem GroundTheory.PAdicHodge.ACris.theta_logTerm {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) :
    theta K p (logTerm hx n) = 0 := by sorry
