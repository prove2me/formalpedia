-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_continuous_coeff
-- name    : GroundTheory.PAdicHodge.AInf.continuous_coeff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:25.938303+00:00
-- url     : https://prove2.me/theorems/1823ad8d-8352-4ad5-9103-9bc1f05d254d
-- title:
--   AInf: continuous coeff
-- statement:
--   The AInf construction uses the continuous coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L157-L160

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

theorem GroundTheory.PAdicHodge.AInf.continuous_coeff (i : ℕ) :
    @Continuous (AInf K p) 𝒪♭ (weakTopology K p) _ fun y => y.coeff i := by sorry
