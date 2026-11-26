-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_continuous_frobeniusEquiv_pAdic
-- name    : GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_pAdic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:55.051563+00:00
-- url     : https://prove2.me/theorems/acaa74ee-ace4-40a5-8015-fa91c6087f5b
-- title:
--   AInf: continuous frobenius Equiv p Adic
-- statement:
--   The AInf construction uses the continuous frobenius Equiv p Adic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L460-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L460-L462

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

theorem GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_pAdic :
    @Continuous (AInf K p) (AInf K p) (pAdicTopology K p) (pAdicTopology K p) (φ) := by sorry
