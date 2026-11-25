-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_singleHom_mem_boxSubgroup
-- name    : GroundTheory.Automorphic.RestrictedTensor.singleHom_mem_boxSubgroup
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:29.406648+00:00
-- url     : https://prove2.me/theorems/7932bdbf-181d-4906-bec5-4287e3e75a71
-- title:
--   Restricted Tensor: single Hom mem box Subgroup
-- statement:
--   The Restricted Tensor construction uses the single Hom mem box Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L66-L74

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

theorem GroundTheory.Automorphic.RestrictedTensor.singleHom_mem_boxSubgroup {K' : ∀ v, Subgroup (G v)} {v : ι} {x : G v}
    (hx : x ∈ K' v) : singleHom K v x ∈ boxSubgroup K K' := by sorry
