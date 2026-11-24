-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_span_teichmuller_pow_iff_norm_le
-- name    : GroundTheory.PAdicHodge.AInf.mem_span_teichmuller_pow_iff_norm_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:27.612486+00:00
-- url     : https://prove2.me/theorems/64011a39-bca2-43c3-be87-357569233028
-- title:
--   AInf: mem span teichmuller pow iff norm le
-- statement:
--   The AInf construction uses the mem span teichmuller pow iff norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L98-L101

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

theorem GroundTheory.PAdicHodge.AInf.mem_span_teichmuller_pow_iff_norm_le (ϖ : 𝒪♭) (n : ℕ) (d : AInf K p) :
    d ∈ Ideal.span {teichmuller p ϖ} ^ n ↔ ∀ i, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ (n * p ^ i) := by sorry
