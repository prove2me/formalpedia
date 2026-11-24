-- Prove2me | Theorems.Thm_GlobalTheory_SymmetricSimilarTranspose_exists_bilin_cyclic
-- name    : GlobalTheory.SymmetricSimilarTranspose.exists_bilin_cyclic
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:47.916786+00:00
-- url     : https://prove2.me/theorems/2f8744ee-83d9-418c-a593-8d501f13e700
-- title:
--   Symmetric Similar Transpose: exists bilin cyclic
-- statement:
--   The Symmetric Similar Transpose construction uses the exists bilin cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixConjTransposeBySymmetricTausskyZassenhaus.lean#L8-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixConjTransposeBySymmetricTausskyZassenhaus.lean#L8-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBilinCyclic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhaus
import Theorems.Thm_GlobalTheory_SimilarTranspose_exists_bilin_cyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SymmetricSimilarTranspose

theorem GlobalTheory.SymmetricSimilarTranspose.exists_bilin_cyclic {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ B : (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] k,
      (∀ x y, B ((X : k[X]) • x) y = B x ((X : k[X]) • y)) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
        ∀ x y, B x y = B y x := by sorry
