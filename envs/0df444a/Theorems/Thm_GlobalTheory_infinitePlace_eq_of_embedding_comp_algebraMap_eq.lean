-- Prove2me | Theorems.Thm_GlobalTheory_infinitePlace_eq_of_embedding_comp_algebraMap_eq
-- name    : GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:08.257735+00:00
-- url     : https://prove2.me/theorems/3cd8c7f6-18cd-4c1f-b4ed-bcc329778504
-- title:
--   Global Theory: infinite Place eq of embedding comp algebra Map eq
-- statement:
--   The Global Theory construction uses the infinite Place eq of embedding comp algebra Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InfinitePlaceEqOfEmbeddingCompAlgebraMapEq.lean#L6-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InfinitePlaceEqOfEmbeddingCompAlgebraMapEq.lean#L6-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InfinitePlaceEqOfEmbeddingCompAlgebraMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E)
    (h : w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E)) : w₁ = w₂ := by sorry
