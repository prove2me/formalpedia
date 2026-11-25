-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eraseAt_apply_of_ne
-- name    : GroundTheory.Automorphic.RestrictedTensor.eraseAt_apply_of_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:33.537811+00:00
-- url     : https://prove2.me/theorems/da10b1bf-a739-48b7-a3f7-f069fd32aa07
-- title:
--   Restricted Tensor: erase At apply of ne
-- statement:
--   The Restricted Tensor construction uses the erase At apply of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L47-L50

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

theorem GroundTheory.Automorphic.RestrictedTensor.eraseAt_apply_of_ne {v w : ι} (g : Πʳ w, [G w, K w]) (h : w ≠ v) :
    eraseAt v g w = g w := by sorry
