-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_mem_range_finiteEmbed
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_mem_range_finiteEmbed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:31.839413+00:00
-- url     : https://prove2.me/theorems/cfb70ca0-eeda-4d45-bd01-4798b2bdba64
-- title:
--   Restricted Tensor: exists mem range finite Embed
-- statement:
--   The Restricted Tensor construction uses the exists mem range finite Embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L354-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L354-L373

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

theorem GroundTheory.Automorphic.RestrictedTensor.exists_mem_range_finiteEmbed {ξ : ∀ v, V v} {t : ⨂[ℂ] v, V v}
    (ht : t ∈ restrictedTensor ξ) : ∃ T₀ : Finset ι, ∀ T, T₀ ⊆ T →
      t ∈ LinearMap.range (finiteEmbed ξ T) := by sorry
