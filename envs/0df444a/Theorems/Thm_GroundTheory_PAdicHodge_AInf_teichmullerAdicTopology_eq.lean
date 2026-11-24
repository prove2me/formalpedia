-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_teichmullerAdicTopology_eq
-- name    : GroundTheory.PAdicHodge.AInf.teichmullerAdicTopology_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:21.353376+00:00
-- url     : https://prove2.me/theorems/7b83cb55-7183-4924-b15e-4cba0ba9e1c2
-- title:
--   AInf: teichmuller Adic Topology eq
-- statement:
--   The AInf construction uses the teichmuller Adic Topology eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L242-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L242-L245

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

theorem GroundTheory.PAdicHodge.AInf.teichmullerAdicTopology_eq (ϖ ϖ' : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) (hϖ0' : ϖ' ≠ 0)
    (hϖ1' : ‖ϖ'‖ < 1) :
    teichmullerAdicTopology (K := K) ϖ = teichmullerAdicTopology ϖ' := by sorry
