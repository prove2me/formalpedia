-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_pow_p_lt_one
-- name    : GroundTheory.PAdicHodge.AInf.norm_pow_p_lt_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:36.611327+00:00
-- url     : https://prove2.me/theorems/ba662f14-905b-4cf5-9c3e-f9131b2076bd
-- title:
--   AInf: norm pow p lt one
-- statement:
--   The AInf construction uses the norm pow p lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L472-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L472-L474

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

theorem GroundTheory.PAdicHodge.AInf.norm_pow_p_lt_one (ϖ : 𝒪♭) (hϖ1 : ‖ϖ‖ < 1) : ‖ϖ ^ p‖ < 1 := by sorry
