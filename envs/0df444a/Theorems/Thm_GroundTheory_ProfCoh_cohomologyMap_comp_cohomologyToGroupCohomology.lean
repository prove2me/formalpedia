-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_cohomologyMap_comp_cohomologyToGroupCohomology
-- name    : GroundTheory.ProfCoh.cohomologyMap_comp_cohomologyToGroupCohomology
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:06.785983+00:00
-- url     : https://prove2.me/theorems/908e4686-dc21-4a0f-880c-c6347065676d
-- title:
--   Prof Coh: cohomology Map comp cohomology To Group Cohomology
-- statement:
--   The Prof Coh construction uses the cohomology Map comp cohomology To Group Cohomology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L133-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L133-L142

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : Rep.{u} k G) [IsDiscreteRep A]

theorem GroundTheory.ProfCoh.cohomologyMap_comp_cohomologyToGroupCohomology {B : Rep.{u} k G} [IsDiscreteRep B]
    (f : A ⟶ B) (n : ℕ) :
    cohomologyMap f n ≫ cohomologyToGroupCohomology B n =
      cohomologyToGroupCohomology A n ≫ groupCohomology.map (MonoidHom.id G) f n := by sorry
