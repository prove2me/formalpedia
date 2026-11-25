-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_isSymm_of_form
-- name    : GroundTheory.Automorphic.ContragredientTranspose.exists_isSymm_of_form
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:02.241669+00:00
-- url     : https://prove2.me/theorems/6d783419-9370-460b-bbbe-c0e255cd452d
-- title:
--   Contragredient Transpose: exists is Symm of form
-- statement:
--   The Contragredient Transpose construction uses the exists is Symm of form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L308-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L308-L370

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
open scoped Matrix
variable {F : Type u} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.ContragredientTranspose.exists_isSymm_of_form (A : Matrix (Fin n) (Fin n) F) (B : (Fin n → F) → (Fin n → F) → F)
    (hBsymm : ∀ v w, B v w = B w v) (hBaddl : ∀ v v' w, B (v + v') w = B v w + B v' w)
    (hBsmull : ∀ (c : F) v w, B (c • v) w = c * B v w)
    (hBA : ∀ v w, B (A.mulVec v) w = B v (A.mulVec w))
    (hBnd : ∀ w, (∀ v, B v w = 0) → w = 0) :
    ∃ S : GL (Fin n) F, (S : Matrix (Fin n) (Fin n) F).IsSymm ∧
      (S : Matrix (Fin n) (Fin n) F) * A = Aᵀ * S := by sorry
