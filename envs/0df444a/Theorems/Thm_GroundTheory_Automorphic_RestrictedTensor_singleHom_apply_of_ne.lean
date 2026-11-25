-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_singleHom_apply_of_ne
-- name    : GroundTheory.Automorphic.RestrictedTensor.singleHom_apply_of_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:15.000308+00:00
-- url     : https://prove2.me/theorems/ea871c82-9bc0-47cb-a1e9-2c1925f815b6
-- title:
--   Restricted Tensor: single Hom apply of ne
-- statement:
--   The Restricted Tensor construction uses the single Hom apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L32-L33

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Module Set
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
variable [DecidableEq ι]

theorem GroundTheory.Automorphic.RestrictedTensor.singleHom_apply_of_ne {v w : ι} (x : G v) (h : w ≠ v) : singleHom K v x w = 1 := by sorry
