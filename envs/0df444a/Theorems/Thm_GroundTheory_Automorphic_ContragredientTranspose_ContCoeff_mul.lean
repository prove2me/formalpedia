-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_mul
-- name    : GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:50.740495+00:00
-- url     : https://prove2.me/theorems/fe4b1da3-ed17-4cf1-a4c9-3edd8f90ca1f
-- title:
--   Cont Coeff: mul
-- statement:
--   The Cont Coeff construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L143-L146

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

theorem GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.mul {P Q : α → F[X]} (hP : ContCoeff P) (hQ : ContCoeff Q) :
    ContCoeff fun a => P a * Q a := by sorry
