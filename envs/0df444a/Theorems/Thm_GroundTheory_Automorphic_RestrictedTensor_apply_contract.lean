-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_apply_contract
-- name    : GroundTheory.Automorphic.RestrictedTensor.apply_contract
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:00.035801+00:00
-- url     : https://prove2.me/theorems/9f7064b0-a999-496e-9a4c-a1902d3e4b00
-- title:
--   Restricted Tensor: apply contract
-- statement:
--   The Restricted Tensor construction uses the apply contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L262-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L262-L275

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
variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem GroundTheory.Automorphic.RestrictedTensor.apply_contract {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} (v : ι) (t : ⨂[ℂ] w, V w) :
    l v (contract ξ l hl v t) = evalForm ξ l hl t := by sorry
