-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contract_tensorRep_single
-- name    : GroundTheory.Automorphic.RestrictedTensor.contract_tensorRep_single
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:41.249676+00:00
-- url     : https://prove2.me/theorems/3692add0-117d-4fb9-821f-1549d685af53
-- title:
--   Restricted Tensor: contract tensor Rep single
-- statement:
--   The Restricted Tensor construction uses the contract tensor Rep single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Uniqueness.lean#L17-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Uniqueness.lean#L17-L37

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Uniqueness
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
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
  {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

theorem GroundTheory.Automorphic.RestrictedTensor.contract_tensorRep_single [DecidableEq ι] (π : ∀ v, Representation ℂ (G v) (V v))
    {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)} (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) (v : ι)
    (g : G v) (t : ⨂[ℂ] w, V w) :
    contract ξ l hl v (tensorRep K π (singleHom K v g) t) = π v g (contract ξ l hl v t) := by sorry
