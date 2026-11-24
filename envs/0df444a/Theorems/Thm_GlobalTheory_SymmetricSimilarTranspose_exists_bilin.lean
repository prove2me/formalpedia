-- Prove2me | Theorems.Thm_GlobalTheory_SymmetricSimilarTranspose_exists_bilin
-- name    : GlobalTheory.SymmetricSimilarTranspose.exists_bilin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:51.806127+00:00
-- url     : https://prove2.me/theorems/9dc0dd63-dbfe-4e13-9305-b92c595156bf
-- title:
--   Symmetric Similar Transpose: exists bilin
-- statement:
--   The Symmetric Similar Transpose construction uses the exists bilin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixConjTransposeBySymmetricTausskyZassenhaus.lean#L35-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixConjTransposeBySymmetricTausskyZassenhaus.lean#L35-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBilinCyclic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhaus
import Theorems.Thm_GlobalTheory_SimilarTranspose_exists_bilin

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

theorem GlobalTheory.SymmetricSimilarTranspose.exists_bilin {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : W →ₗ[k] W) :
    ∃ B : W →ₗ[k] W →ₗ[k] k, (∀ x y, B (T x) y = B x (T y)) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ x y, B x y = B y x := by sorry
