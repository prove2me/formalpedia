-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_hasSum_teichmuller_coeff
-- name    : GroundTheory.PAdicHodge.AInf.hasSum_teichmuller_coeff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:51.875168+00:00
-- url     : https://prove2.me/theorems/56fde489-8601-427b-a403-7a131f39103a
-- title:
--   AInf: has Sum teichmuller coeff
-- statement:
--   The AInf construction uses the has Sum teichmuller coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L403-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L403-L409

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

theorem GroundTheory.PAdicHodge.AInf.hasSum_teichmuller_coeff (x : AInf K p) :
    @HasSum (AInf K p) ℕ _ (pAdicTopology K p)
      (fun n => teichmuller p (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n)) *
        (p : AInf K p) ^ n) x (SummationFilter.unconditional ℕ) := by sorry
