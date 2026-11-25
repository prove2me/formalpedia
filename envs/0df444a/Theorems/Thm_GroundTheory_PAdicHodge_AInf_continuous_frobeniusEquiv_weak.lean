-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_continuous_frobeniusEquiv_weak
-- name    : GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_weak
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:47.219147+00:00
-- url     : https://prove2.me/theorems/3a881d69-a09b-419b-adf8-982908c5cbb6
-- title:
--   AInf: continuous frobenius Equiv weak
-- statement:
--   The AInf construction uses the continuous frobenius Equiv weak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L490-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L490-L495

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

theorem GroundTheory.PAdicHodge.AInf.continuous_frobeniusEquiv_weak (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @Continuous (AInf K p) (AInf K p) (weakTopology K p) (weakTopology K p) (φ) := by sorry
