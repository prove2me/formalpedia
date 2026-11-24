-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_sumForm_add_left
-- name    : GroundTheory.Automorphic.ContragredientTranspose.sumForm_add_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:02.985155+00:00
-- url     : https://prove2.me/theorems/da3c52da-9a67-4793-bcc1-0acfb848c4c4
-- title:
--   Contragredient Transpose: sum Form add left
-- statement:
--   The Contragredient Transpose construction uses the sum Form add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L257-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L257-L262

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

theorem GroundTheory.Automorphic.ContragredientTranspose.sumForm_add_left (x x' y : CycSum q) :
    sumForm q hq (x + x') y = sumForm q hq x y + sumForm q hq x' y := by sorry
