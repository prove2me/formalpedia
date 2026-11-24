-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coindCokernelSection_mk
-- name    : GroundTheory.ProfCoh.coindCokernelSection_mk
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:31.830558+00:00
-- url     : https://prove2.me/theorems/d303ba32-d8cc-4142-b83c-12cd4dd5c214
-- title:
--   Prof Coh: coind Cokernel Section mk
-- statement:
--   The Prof Coh construction uses the coind Cokernel Section mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules.lean#L179-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules.lean#L179-L182

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
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
open CategoryTheory Filter Topology
universe u
variable (k G : Type u) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [AddCommGroup X] [Module k X]
variable {k G}

theorem GroundTheory.ProfCoh.coindCokernelSection_mk (A : Rep.{u} k G) [IsDiscreteRep A] (f : LocallyConstant G A) :
    coindCokernelSection A (Submodule.Quotient.mk f) =
      f - (coindEmbedding A).hom (coindEval k G A f) := by sorry
