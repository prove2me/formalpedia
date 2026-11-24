-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_lcoeffMod_C_mul
-- name    : GroundTheory.Automorphic.ContragredientTranspose.lcoeffMod_C_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:43.761445+00:00
-- url     : https://prove2.me/theorems/66f92059-b587-4687-b4c8-a88f44082450
-- title:
--   Contragredient Transpose: lcoeff Mod C mul
-- statement:
--   The Contragredient Transpose construction uses the lcoeff Mod C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L37-L39

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

theorem GroundTheory.Automorphic.ContragredientTranspose.lcoeffMod_C_mul (q : F[X]) (c : F) (f : F[X]) :
    lcoeffMod q (C c * f) = c * lcoeffMod q f := by sorry
