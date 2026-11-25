-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCoindIso_naturality
-- name    : GroundTheory.GroupCoh.tateCoindIso_naturality
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:56.744221+00:00
-- url     : https://prove2.me/theorems/88dcd87e-f60d-4736-9685-780dfb88d0f4
-- title:
--   Group Coh: tate Coind Iso naturality
-- statement:
--   The Group Coh construction uses the tate Coind Iso naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L388-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L388-L391

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

theorem GroundTheory.GroupCoh.tateCoindIso_naturality {B B' : Rep.{u} k S} (f : B ⟶ B') (n : ℤ) :
    (tateCohomologyFunctor n).map (coindMap S.subtype f) ≫ (tateCoindIso S B' n).hom =
      (tateCoindIso S B n).hom ≫ (tateCohomologyFunctor n).map f := by sorry
