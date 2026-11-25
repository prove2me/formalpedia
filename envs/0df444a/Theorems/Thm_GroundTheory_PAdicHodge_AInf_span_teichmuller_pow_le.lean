-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_span_teichmuller_pow_le
-- name    : GroundTheory.PAdicHodge.AInf.span_teichmuller_pow_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:36.599866+00:00
-- url     : https://prove2.me/theorems/aef01f58-3dac-4871-8343-b08d2e7c7ce7
-- title:
--   AInf: span teichmuller pow le
-- statement:
--   The AInf construction uses the span teichmuller pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L224-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L224-L230

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

theorem GroundTheory.PAdicHodge.AInf.span_teichmuller_pow_le {ϖ ϖ' : 𝒪♭} {m n : ℕ} (h : ‖ϖ‖ ^ m ≤ ‖ϖ'‖ ^ n) :
    Ideal.span {teichmuller p ϖ} ^ m ≤ Ideal.span {(teichmuller p ϖ' : AInf K p)} ^ n := by sorry
