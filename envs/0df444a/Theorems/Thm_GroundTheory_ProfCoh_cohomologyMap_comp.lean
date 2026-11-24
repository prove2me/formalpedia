-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_cohomologyMap_comp
-- name    : GroundTheory.ProfCoh.cohomologyMap_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:56:53.379717+00:00
-- url     : https://prove2.me/theorems/e795c8ef-d58c-47bc-9fec-3e9e04406f1b
-- title:
--   Prof Coh: cohomology Map comp
-- statement:
--   The Prof Coh construction uses the cohomology Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L83-L86

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
variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

theorem GroundTheory.ProfCoh.cohomologyMap_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    cohomologyMap (f ≫ g) n = cohomologyMap f n ≫ cohomologyMap g n := by sorry
