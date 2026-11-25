-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleMap_ideleMap_comp_finiteEmbedding
-- name    : GroundTheory.Global.IdeleMap.ideleMap_comp_finiteEmbedding
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:19:02.264525+00:00
-- url     : https://prove2.me/theorems/d546cdb6-4186-461b-a971-b3d6f25c3ad1
-- title:
--   Idele Map: idele Map comp finite Embedding
-- statement:
--   The Idele Map construction uses the idele Map comp finite Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/Abstract.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/Abstract.lean#L76-L78

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

theorem GroundTheory.Global.IdeleMap.ideleMap_comp_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) :
    (ideleMap φ φinf hφ).comp (finiteEmbedding v) = φ v := by sorry
