-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_lift_adjoin_heckeOps
-- name    : GroundTheory.Automorphic.RestrictedTensor.lift_adjoin_heckeOps
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:56:15.778741+00:00
-- url     : https://prove2.me/theorems/56ebc1d4-f764-407a-b011-e8c07ac5ea98
-- title:
--   Restricted Tensor: lift adjoin hecke Ops
-- statement:
--   The Restricted Tensor construction uses the lift adjoin hecke Ops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L134-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L134-L195

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible
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
open PiTensorProduct Filter Function Module Set Topology
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}
variable (hπ : ∀ v, IsSmooth (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
  [DecidableEq ι] (S : Finset ι) (hSK : ∀ v ∉ S, K' v = K v)
  (hSξ : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (K v))
include hπ hK'c hK'o hK'e

theorem GroundTheory.Automorphic.RestrictedTensor.lift_adjoin_heckeOps (v : S) {a : End ℂ (fixedVectors (π v) (K' v))}
    (ha : a ∈ Algebra.adjoin ℂ (heckeOps (hπ v) (hK'c v) (hK'o v))) :
    ∃ A ∈ Algebra.adjoin ℂ (heckeOps (isSmooth_restrictedTensorRep hπ hξ)
        (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)),
      ∀ t, A (windowEmbedFixed hξ S hSK hSξ t) =
        windowEmbedFixed hξ S hSK hSξ
          (PiTensorProduct.map (Function.update (fun _ => LinearMap.id) v a) t) := by sorry
