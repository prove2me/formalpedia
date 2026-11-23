-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ellQ_mk
-- name    : GroundTheory.Automorphic.ContragredientTranspose.ellQ_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:03.033609+00:00
-- url     : https://prove2.me/theorems/b95d91d2-e88c-4a22-b178-5538ec0ebb2e
-- title:
--   Contragredient Transpose: ell Q mk
-- statement:
--   The Contragredient Transpose construction uses the ell Q mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L89-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L89-L89

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

theorem GroundTheory.Automorphic.ContragredientTranspose.ellQ_mk (f : F[X]) : ellQ q hq (Submodule.Quotient.mk f) = lcoeffMod q f := by sorry
