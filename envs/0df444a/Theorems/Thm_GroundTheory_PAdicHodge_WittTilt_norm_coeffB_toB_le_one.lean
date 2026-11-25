-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_norm_coeffB_toB_le_one
-- name    : GroundTheory.PAdicHodge.WittTilt.norm_coeffB_toB_le_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:26:07.893365+00:00
-- url     : https://prove2.me/theorems/1f2541e0-a5de-58cc-a1ec-a47e1e47c43f
-- title:
--   Witt Tilt: norm coeff B to B le one
-- statement:
--   The Witt Tilt construction uses the norm coeff B to B le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonSlope.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonSlope.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonSlope
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
open _root_.WittVector Laurent Filter Topology
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem GroundTheory.PAdicHodge.WittTilt.norm_coeffB_toB_le_one (z : 𝔸) (n : ℤ) : ‖(teichLift K p).coeffB (toB K p z) n‖ ≤ 1 := by sorry
