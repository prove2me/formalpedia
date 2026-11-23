-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_mk_mul_mk
-- name    : GroundTheory.Automorphic.ContragredientTranspose.mk_mul_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:24.675653+00:00
-- url     : https://prove2.me/theorems/30394691-4094-4de5-bfb9-46cd84932b96
-- title:
--   Contragredient Transpose: mk mul mk
-- statement:
--   The Contragredient Transpose construction uses the mk mul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L92-L94

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

theorem GroundTheory.Automorphic.ContragredientTranspose.mk_mul_mk (f g : F[X]) :
    (Submodule.Quotient.mk f : F[X] ⧸ F[X] ∙ q) * Submodule.Quotient.mk g =
      Submodule.Quotient.mk (f * g) := by sorry
