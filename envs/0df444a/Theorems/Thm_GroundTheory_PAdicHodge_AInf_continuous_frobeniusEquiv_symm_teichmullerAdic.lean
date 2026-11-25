-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_continuous_frobeniusEquiv_symm_teichmullerAdic
-- name    : GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_symm_teichmullerAdic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:10.625372+00:00
-- url     : https://prove2.me/theorems/10ba3512-8e73-4322-8fe8-478bd0ac4fcc
-- title:
--   AInf: continuous frobenius Equiv symm teichmuller Adic
-- statement:
--   The AInf construction uses the continuous frobenius Equiv symm teichmuller Adic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L482-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L482-L488

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

theorem GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_symm_teichmullerAdic (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @Continuous (AInf K p) (AInf K p) (teichmullerAdicTopology ϖ) (teichmullerAdicTopology ϖ)
      (φ).symm := by sorry
