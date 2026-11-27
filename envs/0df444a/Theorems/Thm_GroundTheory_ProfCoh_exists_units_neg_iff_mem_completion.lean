-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_units_neg_iff_mem_completion
-- name    : GroundTheory.ProfCoh.exists_units_neg_iff_mem_completion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:08.007034+00:00
-- url     : https://prove2.me/theorems/338e004c-48fb-55df-aeea-1d53c6df484e
-- title:
--   Prof Coh: exists units neg iff mem completion
-- statement:
--   The Prof Coh construction uses the exists units neg iff mem completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/ExtensionEmbeddingOfIsRealAlgebraMap.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/ExtensionEmbeddingOfIsRealAlgebraMap.lean#L77-L82

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_ExtensionEmbeddingOfIsRealAlgebraMap
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
open NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.ProfCoh.exists_units_neg_iff_mem_completion (S : Set {v : InfinitePlace K // v.IsReal}) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (Completion.extensionEmbeddingOfIsReal v.2 (algebraMap K v.1.Completion (a : K)) < 0 ↔ v ∈ S) ∧
      (0 < Completion.extensionEmbeddingOfIsReal v.2 (algebraMap K v.1.Completion (a : K)) ↔ v ∉ S) := by sorry
