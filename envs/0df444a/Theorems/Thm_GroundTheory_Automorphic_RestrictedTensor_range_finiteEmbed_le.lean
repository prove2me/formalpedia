-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_range_finiteEmbed_le
-- name    : GroundTheory.Automorphic.RestrictedTensor.range_finiteEmbed_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:47.908141+00:00
-- url     : https://prove2.me/theorems/d684e2db-7f75-43a9-aa51-da4ab1e9489e
-- title:
--   Restricted Tensor: range finite Embed le
-- statement:
--   The Restricted Tensor construction uses the range finite Embed le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L302-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean#L302-L309

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

theorem GroundTheory.Automorphic.RestrictedTensor.range_finiteEmbed_le (ξ : ∀ v, V v) (T : Finset ι) :
    LinearMap.range (finiteEmbed ξ T) ≤ restrictedTensor ξ := by sorry
