-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteEmbedding_mem_localEmbeddingSubgroup
-- name    : GroundTheory.Global.IdeleGroup.finiteEmbedding_mem_localEmbeddingSubgroup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:17:48.080835+00:00
-- url     : https://prove2.me/theorems/07e38e69-d8eb-4214-a6b0-d483d4772017
-- title:
--   Idele Group: finite Embedding mem local Embedding Subgroup
-- statement:
--   The Idele Group construction uses the finite Embedding mem local Embedding Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/AbstractUnique.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/AbstractUnique.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_AbstractUnique
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
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem GroundTheory.Global.IdeleGroup.finiteEmbedding_mem_localEmbeddingSubgroup (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : finiteEmbedding v a ∈ localEmbeddingSubgroup K := by sorry
