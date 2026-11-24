-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_finiteEmbed_tprod
-- name    : GroundTheory.Automorphic.RestrictedTensor.finiteEmbed_tprod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:43.110953+00:00
-- url     : https://prove2.me/theorems/4b26dafb-b1c7-4ec1-ac78-2159f843480e
-- title:
--   Restricted Tensor: finite Embed tprod
-- statement:
--   The Restricted Tensor construction uses the finite Embed tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L297-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L297-L300

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
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
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable [DecidableEq ι]

theorem GroundTheory.Automorphic.RestrictedTensor.finiteEmbed_tprod (ξ : ∀ v, V v) (T : Finset ι) (y : ∀ v : T, V v) :
    finiteEmbed ξ T (tprod ℂ y) = tprod ℂ (extend ξ T y) := by sorry
