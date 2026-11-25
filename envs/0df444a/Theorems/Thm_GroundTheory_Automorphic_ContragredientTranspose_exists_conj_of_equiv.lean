-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_conj_of_equiv
-- name    : GroundTheory.Automorphic.ContragredientTranspose.exists_conj_of_equiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:19.945794+00:00
-- url     : https://prove2.me/theorems/ff2a9cfb-630a-4102-820f-e0f670b282f1
-- title:
--   Contragredient Transpose: exists conj of equiv
-- statement:
--   The Contragredient Transpose construction uses the exists conj of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L412-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L412-L457

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

theorem GroundTheory.Automorphic.ContragredientTranspose.exists_conj_of_equiv {x y : GL (Fin n) F}
    (E : Module.AEval' (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)) ≃ₗ[F[X]]
      Module.AEval' (Matrix.toLin' (y : Matrix (Fin n) (Fin n) F))) :
    ∃ g : GL (Fin n) F, x = g * y * g⁻¹ := by sorry
