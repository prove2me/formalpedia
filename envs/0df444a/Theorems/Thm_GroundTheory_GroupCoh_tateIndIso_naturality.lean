-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateIndIso_naturality
-- name    : GroundTheory.GroupCoh.tateIndIso_naturality
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:32.412544+00:00
-- url     : https://prove2.me/theorems/f2e20d74-92a1-4a15-bb0c-0b660e8b0b79
-- title:
--   Group Coh: tate Ind Iso naturality
-- statement:
--   The Group Coh construction uses the tate Ind Iso naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L424-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L424-L427

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
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
open CategoryTheory Limits groupCohomology groupHomology Rep HomologicalComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]

theorem GroundTheory.GroupCoh.tateIndIso_naturality {B B' : Rep.{u} k S} (f : B ⟶ B') (n : ℤ) :
    (tateCohomologyFunctor n).map ((indFunctor k S.subtype).map f) ≫ (tateIndIso S B' n).hom =
      (tateIndIso S B n).hom ≫ (tateCohomologyFunctor n).map f := by sorry
