-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_exists_iotaQ_ne_zero
-- name    : GroundTheory.PAdicHodge.WittTilt.exists_iotaQ_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:46.600347+00:00
-- url     : https://prove2.me/theorems/6aaf51c2-d604-5eda-8802-1e28f9e40b04
-- title:
--   Witt Tilt: exists iota Q ne zero
-- statement:
--   The Witt Tilt construction uses the exists iota Q ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L110-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L110-L121

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
variable {ρ : ℝ}

theorem GroundTheory.PAdicHodge.WittTilt.exists_iotaQ_ne_zero {a : ACris K p} (ha : a ≠ 0) : ∃ m, iotaQ K p (m + 1) a ≠ 0 := by sorry
