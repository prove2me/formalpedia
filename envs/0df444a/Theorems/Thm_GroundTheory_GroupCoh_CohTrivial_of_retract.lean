-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_CohTrivial_of_retract
-- name    : GroundTheory.GroupCoh.CohTrivial.of_retract
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:38.694323+00:00
-- url     : https://prove2.me/theorems/a1f937c1-d509-4f42-a810-a74d3edd916f
-- title:
--   Coh Trivial: of retract
-- statement:
--   The Coh Trivial construction uses the of retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialBasic.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialBasic.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_retract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]

theorem GroundTheory.GroupCoh.CohTrivial.of_retract {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : CohTrivial N) : CohTrivial M := by sorry
