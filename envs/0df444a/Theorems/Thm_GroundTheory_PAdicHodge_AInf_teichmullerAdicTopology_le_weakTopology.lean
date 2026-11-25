-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_teichmullerAdicTopology_le_weakTopology
-- name    : GroundTheory.PAdicHodge.AInf.teichmullerAdicTopology_le_weakTopology
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:27.182402+00:00
-- url     : https://prove2.me/theorems/8455bebb-d6e2-52be-b613-2a9c7e1b6e5e
-- title:
--   AInf: teichmuller Adic Topology le weak Topology
-- statement:
--   The AInf construction uses the teichmuller Adic Topology le weak Topology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L252-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L252-L255

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

theorem GroundTheory.PAdicHodge.AInf.teichmullerAdicTopology_le_weakTopology (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    teichmullerAdicTopology ϖ ≤ weakTopology K p := by sorry
