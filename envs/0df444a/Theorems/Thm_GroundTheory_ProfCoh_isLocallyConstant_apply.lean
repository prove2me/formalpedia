-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isLocallyConstant_apply
-- name    : GroundTheory.ProfCoh.isLocallyConstant_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:13:06.243805+00:00
-- url     : https://prove2.me/theorems/974128a0-629e-4dd8-a2c8-683093b5801b
-- title:
--   Prof Coh: is Locally Constant apply
-- statement:
--   The Prof Coh construction uses the is Locally Constant apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L263-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L263-L273

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
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
open CategoryTheory Limits Topology
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.isLocallyConstant_apply (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    IsLocallyConstant fun g : G => A.ρ g a := by sorry
