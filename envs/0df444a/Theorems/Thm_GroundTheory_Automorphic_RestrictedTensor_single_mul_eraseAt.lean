-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_single_mul_eraseAt
-- name    : GroundTheory.Automorphic.RestrictedTensor.single_mul_eraseAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:29.360222+00:00
-- url     : https://prove2.me/theorems/746212d5-8b52-4058-94fd-72c4f554a2f0
-- title:
--   Restricted Tensor: single mul erase At
-- statement:
--   The Restricted Tensor construction uses the single mul erase At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L52-L54

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

theorem GroundTheory.Automorphic.RestrictedTensor.single_mul_eraseAt (v : ι) (g : Πʳ w, [G w, K w]) :
    singleHom K v (g v) * eraseAt v g = g := by sorry
