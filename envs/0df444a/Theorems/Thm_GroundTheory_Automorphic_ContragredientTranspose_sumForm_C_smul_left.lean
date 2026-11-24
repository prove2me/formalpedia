-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_sumForm_C_smul_left
-- name    : GroundTheory.Automorphic.ContragredientTranspose.sumForm_C_smul_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:02.639113+00:00
-- url     : https://prove2.me/theorems/90a57f9c-7e93-45e1-9cab-056ff919a419
-- title:
--   Contragredient Transpose: sum Form C smul left
-- statement:
--   The Contragredient Transpose construction uses the sum Form C smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L265-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L265-L270

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

theorem GroundTheory.Automorphic.ContragredientTranspose.sumForm_C_smul_left (c : F) (x y : CycSum q) :
    sumForm q hq (C c • x) y = c * sumForm q hq x y := by sorry
