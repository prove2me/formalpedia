-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_log_congr
-- name    : GroundTheory.PAdicHodge.ACris.log_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:28:53.707943+00:00
-- url     : https://prove2.me/theorems/b08f47e5-6329-43b7-ad0b-9d65d44f2d53
-- title:
--   ACris: log congr
-- statement:
--   The ACris construction uses the log congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L220-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L220-L222

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
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
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}
variable {x : AInf K p}

theorem GroundTheory.PAdicHodge.ACris.log_congr {x y : AInf K p} (h : x = y) (hx : x ∈ RingHom.ker θ) (hy : y ∈ RingHom.ker θ) :
    log hx = log hy := by sorry
