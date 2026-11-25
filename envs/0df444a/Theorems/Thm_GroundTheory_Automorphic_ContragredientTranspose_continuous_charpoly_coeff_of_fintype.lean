-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_continuous_charpoly_coeff_of_fintype
-- name    : GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff_of_fintype
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:12.32331+00:00
-- url     : https://prove2.me/theorems/c98cf9bc-350a-4e31-8a83-fe24b250a246
-- title:
--   Contragredient Transpose: continuous charpoly coeff of fintype
-- statement:
--   The Contragredient Transpose construction uses the continuous charpoly coeff of fintype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L183-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L183-L198

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
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff_of_fintype (k : ℕ) :
    Continuous fun A : Matrix m m F => A.charpoly.coeff k := by sorry
