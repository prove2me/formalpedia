-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_map_frobeniusEquiv_symm_span_teichmuller_pow
-- name    : GroundTheory.PAdicHodge.AInf.map_frobeniusEquiv_symm_span_teichmuller_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:20.565984+00:00
-- url     : https://prove2.me/theorems/957f3bbd-f050-4955-a74e-8c5ec7c735aa
-- title:
--   AInf: map frobenius Equiv symm span teichmuller pow
-- statement:
--   The AInf construction uses the map frobenius Equiv symm span teichmuller pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L443-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L443-L447

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

theorem GroundTheory.PAdicHodge.AInf.map_frobeniusEquiv_symm_span_teichmuller_pow (ϖ : 𝒪♭) :
    Ideal.map (φ).symm (Ideal.span {(teichmuller p (ϖ ^ p) : AInf K p)}) =
      Ideal.span {(teichmuller p ϖ : AInf K p)} := by sorry
