-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleMap_ideleMap_comp_infiniteEmbedding
-- name    : GroundTheory.Global.IdeleMap.ideleMap_comp_infiniteEmbedding
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:18:56.05564+00:00
-- url     : https://prove2.me/theorems/53c4b8bf-c8e5-440a-bdd2-bdebe6a93373
-- title:
--   Idele Map: idele Map comp infinite Embedding
-- statement:
--   The Idele Map construction uses the idele Map comp infinite Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/Abstract.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/Abstract.lean#L80-L82

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleMap
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
variable (hφ : ∀ᶠ v in cofinite,
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)

theorem GroundTheory.Global.IdeleMap.ideleMap_comp_infiniteEmbedding (w : InfinitePlace K) :
    (ideleMap φ φinf hφ).comp (infiniteEmbedding w) = φinf w := by sorry
