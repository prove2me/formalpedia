-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_asAlgebraHom_eq
-- name    : GroundTheory.Automorphic.RestrictedTensor.exists_asAlgebraHom_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:28.382831+00:00
-- url     : https://prove2.me/theorems/be6003b9-8ce9-47c5-a996-7b98718cb7e1
-- title:
--   Restricted Tensor: exists as Algebra Hom eq
-- statement:
--   The Restricted Tensor construction uses the exists as Algebra Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/OuterTensor.lean#L42-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/OuterTensor.lean#L42-L83

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor
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
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]

theorem GroundTheory.Automorphic.RestrictedTensor.exists_asAlgebraHom_eq {ρ₂ : Representation ℂ M₂ V₂} (hirr : ρ₂.IsIrreducible)
    (hschur : ∀ T : End ℂ V₂, (∀ m, T * ρ₂ m = ρ₂ m * T) → ∃ c : ℂ, T = c • 1)
    (A : End ℂ V₂) (s : Finset V₂) :
    ∃ r : MonoidAlgebra ℂ M₂, ∀ v ∈ s, ρ₂.asAlgebraHom r v = A v := by sorry
