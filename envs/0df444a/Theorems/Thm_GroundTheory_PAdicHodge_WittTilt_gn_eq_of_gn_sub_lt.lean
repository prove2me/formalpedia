-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_gn_eq_of_gn_sub_lt
-- name    : GroundTheory.PAdicHodge.WittTilt.gn_eq_of_gn_sub_lt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:33.859801+00:00
-- url     : https://prove2.me/theorems/8be271b9-1a83-5299-b9f2-7bba9e04a1fa
-- title:
--   Witt Tilt: gn eq of gn sub lt
-- statement:
--   The Witt Tilt construction uses the gn eq of gn sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonApprox.lean#L64-L74

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

theorem GroundTheory.PAdicHodge.WittTilt.gn_eq_of_gn_sub_lt (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {z w : 𝔸}
    (h : gn K p ρ (z - w) < gn K p ρ z) : gn K p ρ w = gn K p ρ z := by sorry
