-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_zsmul
-- name    : GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.zsmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:06.624404+00:00
-- url     : https://prove2.me/theorems/fd9ea299-e73d-40f1-a174-4fec1db218bc
-- title:
--   Cont Coeff: zsmul
-- statement:
--   The Cont Coeff construction uses the zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L159-L164

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

theorem GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.zsmul {P : α → F[X]} (hP : ContCoeff P) (z : ℤ) :
    ContCoeff fun a => z • P a := by sorry
