-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_inflation_comp_cohomologyToGroupCohomology
-- name    : GroundTheory.ProfCoh.inflation_comp_cohomologyToGroupCohomology
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:03:36.106455+00:00
-- url     : https://prove2.me/theorems/edf89865-79cf-4440-a950-bc419312cfb2
-- title:
--   Prof Coh: inflation comp cohomology To Group Cohomology
-- statement:
--   The Prof Coh construction uses the inflation comp cohomology To Group Cohomology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitDefs.lean#L134-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitDefs.lean#L134-L140

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitDefs
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
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
variable (A : Rep.{u} k G)
variable [IsTopologicalGroup G] [IsDiscreteRep A]

theorem GroundTheory.ProfCoh.inflation_comp_cohomologyToGroupCohomology (U : OpenNormalSubgroup G) (n : ℕ) :
    inflation A U n ≫ cohomologyToGroupCohomology A n =
      (groupCohomology.infNatTrans k (U : Subgroup G) n).app A := by sorry
