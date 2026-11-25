-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_finite_monic_dvd
-- name    : GroundTheory.Automorphic.ContragredientTranspose.finite_monic_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:34.732949+00:00
-- url     : https://prove2.me/theorems/7cc62d5d-019a-4579-8734-ae9ffc88bf9f
-- title:
--   Contragredient Transpose: finite monic dvd
-- statement:
--   The Contragredient Transpose construction uses the finite monic dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L459-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L459-L472

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
universe u
variable {F : Type u} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.ContragredientTranspose.finite_monic_dvd {f : F[X]} (hf : f ≠ 0) : {g : F[X] | g.Monic ∧ g ∣ f}.Finite := by sorry
