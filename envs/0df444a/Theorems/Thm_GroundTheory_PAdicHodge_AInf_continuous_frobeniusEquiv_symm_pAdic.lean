-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_continuous_frobeniusEquiv_symm_pAdic
-- name    : GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_symm_pAdic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:42.087347+00:00
-- url     : https://prove2.me/theorems/79503e93-f807-4a7d-8b34-aa70abb5b840
-- title:
--   AInf: continuous frobenius Equiv symm p Adic
-- statement:
--   The AInf construction uses the continuous frobenius Equiv symm p Adic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L464-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L464-L466

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

theorem GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_symm_pAdic :
    @Continuous (AInf K p) (AInf K p) (pAdicTopology K p) (pAdicTopology K p) (φ).symm := by sorry
