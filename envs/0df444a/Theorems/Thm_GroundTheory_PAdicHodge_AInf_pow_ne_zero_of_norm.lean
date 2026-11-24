-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_pow_ne_zero_of_norm
-- name    : GroundTheory.PAdicHodge.AInf.pow_ne_zero_of_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:58.407866+00:00
-- url     : https://prove2.me/theorems/010a2689-f30b-44f2-b2d4-abc08090f589
-- title:
--   AInf: pow ne zero of norm
-- statement:
--   The AInf construction uses the pow ne zero of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L468-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L468-L470

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

theorem GroundTheory.PAdicHodge.AInf.pow_ne_zero_of_norm (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) : ϖ ^ p ≠ 0 := by sorry
