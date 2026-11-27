-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_cochainsMap_f_hom_apply
-- name    : GroundTheory.ProfCoh.cochainsMap_f_hom_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:29.155293+00:00
-- url     : https://prove2.me/theorems/53826e55-2268-42d8-ae44-7ae74aafb076
-- title:
--   Prof Coh: cochains Map f hom apply
-- statement:
--   The Prof Coh construction uses the cochains Map f hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains/Functoriality.lean#L38-L40

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

theorem GroundTheory.ProfCoh.cochainsMap_f_hom_apply (f : A ⟶ B) (n : ℕ) (c : locallyConstantCochains A n) :
    ((cochainsMap f).f n).hom c = cochainsMapLinear f n c := by sorry
