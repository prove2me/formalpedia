-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_theta_periodT
-- name    : GroundTheory.PAdicHodge.ACris.theta_periodT
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:12.992207+00:00
-- url     : https://prove2.me/theorems/40046a13-7061-47ef-bbdb-7ea3a48fc7a6
-- title:
--   ACris: theta period T
-- statement:
--   The ACris construction uses the theta period T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L213-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L213-L214

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

theorem GroundTheory.PAdicHodge.ACris.theta_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : theta K p (periodT hε) = 0 := by sorry
