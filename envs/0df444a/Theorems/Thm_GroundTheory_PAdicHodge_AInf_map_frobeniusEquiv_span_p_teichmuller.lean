-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_map_frobeniusEquiv_span_p_teichmuller
-- name    : GroundTheory.PAdicHodge.AInf.map_frobeniusEquiv_span_p_teichmuller
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:52.035978+00:00
-- url     : https://prove2.me/theorems/e56e569c-a808-4f89-84a0-ec767f75aeb6
-- title:
--   AInf: map frobenius Equiv span p teichmuller
-- statement:
--   The AInf construction uses the map frobenius Equiv span p teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L449-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L449-L452

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
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem GroundTheory.PAdicHodge.AInf.map_frobeniusEquiv_span_p_teichmuller (ϖ : 𝒪♭) :
    Ideal.map (φ) (Ideal.span {(p : AInf K p), teichmuller p ϖ}) =
      Ideal.span {(p : AInf K p), teichmuller p (ϖ ^ p)} := by sorry
