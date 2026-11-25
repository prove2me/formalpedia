-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_tprod_ne_zero
-- name    : GroundTheory.Automorphic.RestrictedTensor.tprod_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:42:35.082797+00:00
-- url     : https://prove2.me/theorems/c8714c73-d12e-4885-b013-c1ac6bac2e4a
-- title:
--   Restricted Tensor: tprod ne zero
-- statement:
--   The Restricted Tensor construction uses the tprod ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L17-L32

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
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
open PiTensorProduct Filter Function Module Set Topology
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

theorem GroundTheory.Automorphic.RestrictedTensor.tprod_ne_zero {ξ x : ∀ v, V v} (hx : IsRestricted ξ x) (h0 : ∀ v, x v ≠ 0) :
    tprod ℂ x ≠ 0 := by sorry
