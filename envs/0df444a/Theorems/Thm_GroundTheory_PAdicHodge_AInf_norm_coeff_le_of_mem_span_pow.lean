-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_coeff_le_of_mem_span_pow
-- name    : GroundTheory.PAdicHodge.AInf.norm_coeff_le_of_mem_span_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:25.99235+00:00
-- url     : https://prove2.me/theorems/d00fab6f-1405-489d-a85e-17bbae1f1b70
-- title:
--   AInf: norm coeff le of mem span pow
-- statement:
--   The AInf construction uses the norm coeff le of mem span pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L136-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L136-L150

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

theorem GroundTheory.PAdicHodge.AInf.norm_coeff_le_of_mem_span_pow (ϖ : 𝒪♭) (N : ℕ) (d : AInf K p)
    (hd : d ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} ^ (N + N)) :
    ∀ i < N, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ N := by sorry
