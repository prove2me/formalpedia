-- Prove2me | Theorems.Thm_Ideal_continuous_of_map_le
-- name    : Ideal.continuous_of_map_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:37.626468+00:00
-- url     : https://prove2.me/theorems/e5411136-7dc0-4baa-8c6a-a312501a3c60
-- title:
--   Ideal: continuous of map le
-- statement:
--   The Ideal construction uses the continuous of map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L413-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L413-L426

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
omit hp [IsPerfectoidField K p]

theorem Ideal.continuous_of_map_le {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B]
    [RingHomClass F A B] (f : F) {I : Ideal A} {J : Ideal B} (h : I.map f ≤ J) :
    @Continuous A B I.adicTopology J.adicTopology f := by sorry
