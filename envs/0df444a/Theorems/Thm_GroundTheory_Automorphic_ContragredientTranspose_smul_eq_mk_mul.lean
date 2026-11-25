-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_smul_eq_mk_mul
-- name    : GroundTheory.Automorphic.ContragredientTranspose.smul_eq_mk_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:54.945598+00:00
-- url     : https://prove2.me/theorems/f0c53fc9-2e7b-4108-976e-060e613b3c70
-- title:
--   Contragredient Transpose: smul eq mk mul
-- statement:
--   The Contragredient Transpose construction uses the smul eq mk mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L97-L100

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
omit hq

theorem GroundTheory.Automorphic.ContragredientTranspose.smul_eq_mk_mul (r : F[X]) (a : F[X] ⧸ F[X] ∙ q) :
    r • a = Submodule.Quotient.mk r * a := by sorry
