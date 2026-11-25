-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_units_neg_iff_mem
-- name    : GroundTheory.ProfCoh.exists_units_neg_iff_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:22.053807+00:00
-- url     : https://prove2.me/theorems/af7d7e0a-8fcd-4277-bfbb-7832c5b44d13
-- title:
--   Prof Coh: exists units neg iff mem
-- statement:
--   The Prof Coh construction uses the exists units neg iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/ExtensionEmbeddingOfIsRealAlgebraMap.lean#L16-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalClassFormation/ExtensionEmbeddingOfIsRealAlgebraMap.lean#L16-L56

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

theorem GroundTheory.ProfCoh.exists_units_neg_iff_mem (S : Set {v : InfinitePlace K // v.IsReal}) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (embedding_of_isReal v.2 (a : K) < 0 ↔ v ∈ S) ∧ (0 < embedding_of_isReal v.2 (a : K) ↔ v ∉ S) := by sorry
