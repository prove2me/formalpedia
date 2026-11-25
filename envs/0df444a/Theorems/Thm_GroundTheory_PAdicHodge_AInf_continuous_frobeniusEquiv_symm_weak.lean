-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_continuous_frobeniusEquiv_symm_weak
-- name    : GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_symm_weak
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:32.823478+00:00
-- url     : https://prove2.me/theorems/ecaac1e8-723c-518f-9b93-1c104324cecf
-- title:
--   AInf: continuous frobenius Equiv symm weak
-- statement:
--   The AInf construction uses the continuous frobenius Equiv symm weak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L497-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L497-L503

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

theorem GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_symm_weak (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @Continuous (AInf K p) (AInf K p) (weakTopology K p) (weakTopology K p) (φ).symm := by sorry
