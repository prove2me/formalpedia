-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_teichmullerAdicTopology_le
-- name    : GroundTheory.PAdicHodge.AInf.teichmullerAdicTopology_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:43.920815+00:00
-- url     : https://prove2.me/theorems/82c5ac1f-3a5a-46b1-ae8b-b7af60917115
-- title:
--   AInf: teichmuller Adic Topology le
-- statement:
--   The AInf construction uses the teichmuller Adic Topology le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L232-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L232-L240

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

theorem GroundTheory.PAdicHodge.AInf.teichmullerAdicTopology_le (ϖ ϖ' : 𝒪♭) (hϖ1 : ‖ϖ‖ < 1) (hϖ0' : ϖ' ≠ 0) :
    teichmullerAdicTopology (K := K) ϖ ≤ teichmullerAdicTopology ϖ' := by sorry
