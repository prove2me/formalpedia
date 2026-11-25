-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_log_eq_of_isAdicSum
-- name    : GroundTheory.PAdicHodge.ACris.log_eq_of_isAdicSum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:53.854837+00:00
-- url     : https://prove2.me/theorems/07b95509-7123-5a0e-8159-836d7d51391a
-- title:
--   ACris: log eq of is Adic Sum
-- statement:
--   The ACris construction uses the log eq of is Adic Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L183-L185

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

theorem GroundTheory.PAdicHodge.ACris.log_eq_of_isAdicSum {x : AInf K p} {hx : x ∈ RingHom.ker θ} {s : ACris K p}
    (hs : IsAdicSum 𝔭 (logTerm hx) s) : log hx = s := by sorry
