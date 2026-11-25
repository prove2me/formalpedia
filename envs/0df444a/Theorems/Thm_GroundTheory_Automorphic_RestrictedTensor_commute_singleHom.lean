-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_singleHom
-- name    : GroundTheory.Automorphic.RestrictedTensor.commute_singleHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:29.515328+00:00
-- url     : https://prove2.me/theorems/42f56ae9-73af-465c-ae02-e45425e2cdc2
-- title:
--   Restricted Tensor: commute single Hom
-- statement:
--   The Restricted Tensor construction uses the commute single Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L76-L81

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

theorem GroundTheory.Automorphic.RestrictedTensor.commute_singleHom {v : ι} (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    singleHom K v x * b = b * singleHom K v x := by sorry
