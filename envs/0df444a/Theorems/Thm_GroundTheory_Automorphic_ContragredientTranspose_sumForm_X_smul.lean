-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_sumForm_X_smul
-- name    : GroundTheory.Automorphic.ContragredientTranspose.sumForm_X_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:59.031193+00:00
-- url     : https://prove2.me/theorems/129e4999-b86b-4ff3-884e-d68f4ab98e0a
-- title:
--   Contragredient Transpose: sum Form X smul
-- statement:
--   The Contragredient Transpose construction uses the sum Form X smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L273-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L273-L279

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
variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → F[X])
  (hq : ∀ i, q i ≠ 0)
omit [DecidableEq ι]

theorem GroundTheory.Automorphic.ContragredientTranspose.sumForm_X_smul (x y : CycSum q) :
    sumForm q hq ((X : F[X]) • x) y = sumForm q hq x ((X : F[X]) • y) := by sorry
