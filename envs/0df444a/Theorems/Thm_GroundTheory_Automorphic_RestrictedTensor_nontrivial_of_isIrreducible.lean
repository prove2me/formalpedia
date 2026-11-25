-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_nontrivial_of_isIrreducible
-- name    : GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:02.950546+00:00
-- url     : https://prove2.me/theorems/ee798d3d-9d94-4bae-a593-c5bfbe513a83
-- title:
--   Restricted Tensor: nontrivial of is Irreducible
-- statement:
--   The Restricted Tensor construction uses the nontrivial of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L36-L44

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
omit [∀ v, Module ℂ (V v)]

theorem GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible {H : Type*} [Group H] {W : Type*} [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ H W} (h : σ.IsIrreducible) : Nontrivial W := by sorry
