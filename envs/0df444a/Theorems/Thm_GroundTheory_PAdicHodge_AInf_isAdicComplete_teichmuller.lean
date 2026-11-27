-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_isAdicComplete_teichmuller
-- name    : GroundTheory.PAdicHodge.AInf.isAdicComplete_teichmuller
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:42.57805+00:00
-- url     : https://prove2.me/theorems/36e498cb-86cd-5fac-acc8-14c55e7653f7
-- title:
--   AInf: is Adic Complete teichmuller
-- statement:
--   The AInf construction uses the is Adic Complete teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L313-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L313-L363

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p

theorem GroundTheory.PAdicHodge.AInf.isAdicComplete_teichmuller (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    IsAdicComplete (Ideal.span {(teichmuller p ϖ : AInf K p)}) (AInf K p) := by sorry
