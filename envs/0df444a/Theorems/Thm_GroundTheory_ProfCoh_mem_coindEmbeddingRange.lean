-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_coindEmbeddingRange
-- name    : GroundTheory.ProfCoh.mem_coindEmbeddingRange
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:11.964339+00:00
-- url     : https://prove2.me/theorems/0479f233-3b04-475d-baf6-d6a8284bc33a
-- title:
--   Prof Coh: mem coind Embedding Range
-- statement:
--   The Prof Coh construction uses the mem coind Embedding Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules.lean#L126-L128

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

theorem GroundTheory.ProfCoh.mem_coindEmbeddingRange (A : Rep.{u} k G) [IsDiscreteRep A] (f : LocallyConstant G A) :
    f ∈ coindEmbeddingRange A ↔ ∃ a : A, (coindEmbedding A).hom a = f := by sorry
