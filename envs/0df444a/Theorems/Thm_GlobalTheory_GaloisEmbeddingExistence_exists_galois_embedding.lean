-- Prove2me | Theorems.Thm_GlobalTheory_GaloisEmbeddingExistence_exists_galois_embedding
-- name    : GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:44.598849+00:00
-- url     : https://prove2.me/theorems/9969c58c-11ea-5cb2-9dbe-f6ed3300a6a7
-- title:
--   Galois Embedding Existence: exists galois embedding
-- statement:
--   The Galois Embedding Existence construction uses the exists galois embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGaloisEmbedding.lean#L5-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGaloisEmbedding.lean#L5-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGaloisEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GaloisEmbeddingExistence

theorem GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding (R R' : Type) [CommRing R] [IsDomain R] [CharZero R]
    [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R']
    (hinj : Function.Injective (algebraMap R R')) :
    ∃ (L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R))),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
        ∃ (j : R' →ₐ[R] L), Function.Injective j := by sorry
