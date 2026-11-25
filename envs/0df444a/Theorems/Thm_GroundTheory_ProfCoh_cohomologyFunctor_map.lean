-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_cohomologyFunctor_map
-- name    : GroundTheory.ProfCoh.cohomologyFunctor_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:08.708499+00:00
-- url     : https://prove2.me/theorems/8cbfdcb1-5f74-5841-b034-880fbe51a869
-- title:
--   Prof Coh: cohomology Functor map
-- statement:
--   The Prof Coh construction uses the cohomology Functor map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L113-L115

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
variable (k G)

theorem GroundTheory.ProfCoh.cohomologyFunctor_map (n : ℕ) {A B : DiscreteRep.{u} k G} (f : A ⟶ B) :
    (cohomologyFunctor k G n).map f = cohomologyMap f.hom n := by sorry
