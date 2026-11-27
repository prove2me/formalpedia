-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_groupCohomologyPiEquiv_apply
-- name    : GroundTheory.ProfCoh.groupCohomologyPiEquiv_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:17.370467+00:00
-- url     : https://prove2.me/theorems/4c3ddde5-bfd9-4afe-916d-8c8a4133b1ca
-- title:
--   Prof Coh: group Cohomology Pi Equiv apply
-- statement:
--   The Prof Coh construction uses the group Cohomology Pi Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/IdeleCohomology/Product.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/IdeleCohomology/Product.lean#L94-L98

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_FilteredHomology
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_IdeleCohomology_Product
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
open CategoryTheory Limits
universe u
variable {k G : Type u} [CommRing k] [Group G] {ι : Type*} {P : Rep.{u} k G}
  {A : ι → Rep.{u} k G}

theorem GroundTheory.ProfCoh.groupCohomologyPiEquiv_apply (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (n : ℕ)
    (x : groupCohomology P n) (i : ι) :
    groupCohomologyPiEquiv p hp n x i = (groupCohomology.map (MonoidHom.id G) (p i) n).hom x := by sorry

attribute [defeq] GroundTheory.ProfCoh.groupCohomologyPiEquiv_apply
