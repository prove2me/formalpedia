-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nontrivial_of_irreducible
-- name    : GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_irreducible
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:07.921931+00:00
-- url     : https://prove2.me/theorems/b48d2a1e-9a95-45e5-8bc8-1651f795f4a9
-- title:
--   Restricted Tensor: nontrivial of irreducible
-- statement:
--   The Restricted Tensor construction uses the nontrivial of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/OuterTensor.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/OuterTensor.lean#L17-L25

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

theorem GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_irreducible {ρ : Representation ℂ M₁ V₁} (h : ρ.IsIrreducible) :
    Nontrivial V₁ := by sorry
