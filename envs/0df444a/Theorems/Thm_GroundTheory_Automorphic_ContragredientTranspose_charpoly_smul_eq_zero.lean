-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_charpoly_smul_eq_zero
-- name    : GroundTheory.Automorphic.ContragredientTranspose.charpoly_smul_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:01.594591+00:00
-- url     : https://prove2.me/theorems/e15afa17-3243-450a-b463-4518d5d59aa9
-- title:
--   Contragredient Transpose: charpoly smul eq zero
-- statement:
--   The Contragredient Transpose construction uses the charpoly smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L212-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L212-L218

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

theorem GroundTheory.Automorphic.ContragredientTranspose.charpoly_smul_eq_zero (A : Matrix (Fin n) (Fin n) F)
    (m : Module.AEval' (Matrix.toLin' A)) : A.charpoly • m = 0 := by sorry
