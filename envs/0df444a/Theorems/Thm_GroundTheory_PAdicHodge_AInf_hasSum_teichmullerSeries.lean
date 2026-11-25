-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_hasSum_teichmullerSeries
-- name    : GroundTheory.PAdicHodge.AInf.hasSum_teichmullerSeries
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:51.360337+00:00
-- url     : https://prove2.me/theorems/c4b12e8e-a534-4246-aebd-d4f2ecf28461
-- title:
--   AInf: has Sum teichmuller Series
-- statement:
--   The AInf construction uses the has Sum teichmuller Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L365-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L365-L401

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

theorem GroundTheory.PAdicHodge.AInf.hasSum_teichmullerSeries (a : ℕ → 𝒪♭) :
    @HasSum (AInf K p) ℕ _ (pAdicTopology K p) (fun n => teichmuller p (a n) * (p : AInf K p) ^ n)
      (WittVector.teichmullerSeries a) (SummationFilter.unconditional ℕ) := by sorry
