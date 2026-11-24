-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_continuous_charpoly_coeff
-- name    : GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:56.026264+00:00
-- url     : https://prove2.me/theorems/5a8ae009-cd6f-4691-ae4f-7c25042f1c2a
-- title:
--   Contragredient Transpose: continuous charpoly coeff
-- statement:
--   The Contragredient Transpose construction uses the continuous charpoly coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L200-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L200-L202

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
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {α : Type*} [TopologicalSpace α]
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff {n : ℕ} (k : ℕ) :
    Continuous fun A : Matrix (Fin n) (Fin n) F => A.charpoly.coeff k := by sorry
