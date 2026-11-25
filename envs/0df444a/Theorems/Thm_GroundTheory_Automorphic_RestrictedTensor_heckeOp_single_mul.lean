-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_single_mul
-- name    : GroundTheory.Automorphic.RestrictedTensor.heckeOp_single_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:28.070956+00:00
-- url     : https://prove2.me/theorems/aa7453cc-52ef-4b24-9f9d-fdd2b17b4004
-- title:
--   Restricted Tensor: hecke Op single mul
-- statement:
--   The Restricted Tensor construction uses the hecke Op single mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L114-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Places.lean#L114-L131

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isOpen_boxSubgroup

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
open Filter Function Module Set
open scoped RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
variable [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
  [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
  [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))] [hKc : ∀ v, CompactSpace (K v)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}
  (hρ : IsSmooth ρ) {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
variable [DecidableEq ι]
include hK'c hK'o hK'e

theorem GroundTheory.Automorphic.RestrictedTensor.heckeOp_single_mul (v : ι) (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
        (singleHom K v x * b) =
      heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
          (singleHom K v x) *
        heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) b := by sorry
