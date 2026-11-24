-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ellQ_C_smul
-- name    : GroundTheory.Automorphic.ContragredientTranspose.ellQ_C_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:36.65892+00:00
-- url     : https://prove2.me/theorems/8f1394f6-cbc4-430b-8297-2519c2e58c52
-- title:
--   Contragredient Transpose: ell Q C smul
-- statement:
--   The Contragredient Transpose construction uses the ell Q C smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L112-L114

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
variable {F : Type*} [Field F]
variable {q : F[X]} (hq : q ≠ 0)

theorem GroundTheory.Automorphic.ContragredientTranspose.ellQ_C_smul (c : F) (a : F[X] ⧸ F[X] ∙ q) : ellQ q hq (C c • a) = c * ellQ q hq a := by sorry
