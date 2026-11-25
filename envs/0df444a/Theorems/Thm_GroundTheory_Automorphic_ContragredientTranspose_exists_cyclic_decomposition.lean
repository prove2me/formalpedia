-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_cyclic_decomposition
-- name    : GroundTheory.Automorphic.ContragredientTranspose.exists_cyclic_decomposition
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:16.475672+00:00
-- url     : https://prove2.me/theorems/903b956f-656f-43a8-9561-b4f365ec0cb7
-- title:
--   Contragredient Transpose: exists cyclic decomposition
-- statement:
--   The Contragredient Transpose construction uses the exists cyclic decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L220-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L220-L237

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
universe u
variable {F : Type u} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.ContragredientTranspose.exists_cyclic_decomposition (A : Matrix (Fin n) (Fin n) F) :
    ∃ (ι : Type u) (_ : Fintype ι) (q : ι → F[X]), (∀ i, q i ≠ 0) ∧ (∀ i, q i ∣ A.charpoly) ∧
      Nonempty (Module.AEval' (Matrix.toLin' A) ≃ₗ[F[X]] DirectSum ι fun i => F[X] ⧸ F[X] ∙ q i) := by sorry
