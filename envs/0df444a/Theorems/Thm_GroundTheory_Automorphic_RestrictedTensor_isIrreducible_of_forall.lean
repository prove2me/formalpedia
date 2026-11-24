-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isIrreducible_of_forall
-- name    : GroundTheory.Automorphic.RestrictedTensor.isIrreducible_of_forall
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:34:04.173583+00:00
-- url     : https://prove2.me/theorems/3b32028b-ba5b-43f1-b2f4-4486ea8170e0
-- title:
--   Restricted Tensor: is Irreducible of forall
-- statement:
--   The Restricted Tensor construction uses the is Irreducible of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L150-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L150-L187

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
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
open Module Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
omit hρ hKc hKo

theorem GroundTheory.Automorphic.RestrictedTensor.isIrreducible_of_forall (hρ : IsSmooth ρ) [Nontrivial V]
    (h : ∀ x y : V, x ≠ 0 → ∃ (K : Subgroup G) (hKc : IsCompact (K : Set G))
      (hKo : IsOpen (K : Set G)), x ∈ fixedVectors ρ K ∧ y ∈ fixedVectors ρ K ∧
        IsSimpleUnder (heckeOps hρ hKc hKo)) :
    ρ.IsIrreducible := by sorry
