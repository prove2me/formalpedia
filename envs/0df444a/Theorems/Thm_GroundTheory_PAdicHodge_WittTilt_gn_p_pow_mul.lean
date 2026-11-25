-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_p_pow_mul
-- name    : GroundTheory.PAdicHodge.WittTilt.gn_p_pow_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:45.781967+00:00
-- url     : https://prove2.me/theorems/b00a7e30-29c7-4c74-adc2-9567fa349397
-- title:
--   Witt Tilt: gn p pow mul
-- statement:
--   The Witt Tilt construction uses the gn p pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L49-L51

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

theorem GroundTheory.PAdicHodge.WittTilt.gn_p_pow_mul (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) (z : 𝔸) :
    gn K p ρ ((p : 𝔸) ^ N * z) = ρ ^ N * gn K p ρ z := by sorry
