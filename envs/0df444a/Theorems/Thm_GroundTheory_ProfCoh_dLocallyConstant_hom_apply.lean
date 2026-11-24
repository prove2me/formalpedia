-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_dLocallyConstant_hom_apply
-- name    : GroundTheory.ProfCoh.dLocallyConstant_hom_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:02.704995+00:00
-- url     : https://prove2.me/theorems/e7954097-318b-46b3-aca6-52e48e20976b
-- title:
--   Prof Coh: d Locally Constant hom apply
-- statement:
--   The Prof Coh construction uses the d Locally Constant hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains.lean#L83-L87

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
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
variable [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.dLocallyConstant_hom_apply (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ)
    (f : locallyConstantCochains A n) :
    ((dLocallyConstant A n).hom f : (Fin (n + 1) → G) → A) =
      (inhomogeneousCochains.d A n).hom f := by sorry
