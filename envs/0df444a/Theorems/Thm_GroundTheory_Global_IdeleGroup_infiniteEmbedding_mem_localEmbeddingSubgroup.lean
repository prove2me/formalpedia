-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteEmbedding_mem_localEmbeddingSubgroup
-- name    : GroundTheory.Global.IdeleGroup.infiniteEmbedding_mem_localEmbeddingSubgroup
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:19:33.206563+00:00
-- url     : https://prove2.me/theorems/ae3b830f-e21e-47b1-a5a3-fac428489ece
-- title:
--   Idele Group: infinite Embedding mem local Embedding Subgroup
-- statement:
--   The Idele Group construction uses the infinite Embedding mem local Embedding Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/AbstractUnique.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/AbstractUnique.lean#L25-L27

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

theorem GroundTheory.Global.IdeleGroup.infiniteEmbedding_mem_localEmbeddingSubgroup (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ localEmbeddingSubgroup K := by sorry
