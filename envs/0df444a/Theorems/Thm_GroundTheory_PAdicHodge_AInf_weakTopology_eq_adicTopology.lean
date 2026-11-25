-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_weakTopology_eq_adicTopology
-- name    : GroundTheory.PAdicHodge.AInf.weakTopology_eq_adicTopology
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:40.170749+00:00
-- url     : https://prove2.me/theorems/78f2da6f-b2ec-4ea9-8a35-17dd0ce60865
-- title:
--   AInf: weak Topology eq adic Topology
-- statement:
--   The AInf construction uses the weak Topology eq adic Topology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L162-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L162-L216

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

theorem GroundTheory.PAdicHodge.AInf.weakTopology_eq_adicTopology (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    weakTopology K p = (Ideal.span {(p : AInf K p), teichmuller p ϖ}).adicTopology := by sorry
