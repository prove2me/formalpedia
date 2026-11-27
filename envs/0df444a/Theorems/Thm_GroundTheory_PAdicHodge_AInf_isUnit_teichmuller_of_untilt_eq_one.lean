-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_isUnit_teichmuller_of_untilt_eq_one
-- name    : GroundTheory.PAdicHodge.AInf.isUnit_teichmuller_of_untilt_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:47.770563+00:00
-- url     : https://prove2.me/theorems/11a08e54-29a0-59ca-bd0f-148064829516
-- title:
--   AInf: is Unit teichmuller of untilt eq one
-- statement:
--   The AInf construction uses the is Unit teichmuller of untilt eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L265-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L265-L268

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem GroundTheory.PAdicHodge.AInf.isUnit_teichmuller_of_untilt_eq_one {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    IsUnit (teichmuller p ε : AInf K p) := by sorry
