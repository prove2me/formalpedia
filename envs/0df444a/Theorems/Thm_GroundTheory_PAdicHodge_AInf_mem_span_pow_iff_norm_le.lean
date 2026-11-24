-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_span_pow_iff_norm_le
-- name    : GroundTheory.PAdicHodge.AInf.mem_span_pow_iff_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:06.599905+00:00
-- url     : https://prove2.me/theorems/370f6b02-179a-44c6-8e2d-6003224157b2
-- title:
--   AInf: mem span pow iff norm le
-- statement:
--   The AInf construction uses the mem span pow iff norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L84-L86

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

theorem GroundTheory.PAdicHodge.AInf.mem_span_pow_iff_norm_le (ϖ x : 𝒪♭) (k : ℕ) :
    x ∈ Ideal.span {ϖ ^ k} ↔ ‖x‖ ≤ ‖ϖ‖ ^ k := by sorry
