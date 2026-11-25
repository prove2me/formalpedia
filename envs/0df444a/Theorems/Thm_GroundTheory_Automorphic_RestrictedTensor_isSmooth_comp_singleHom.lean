-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSmooth_comp_singleHom
-- name    : GroundTheory.Automorphic.RestrictedTensor.isSmooth_comp_singleHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:01.834856+00:00
-- url     : https://prove2.me/theorems/f6ff0e63-ea02-43b9-a42e-4d27eaa2fe6c
-- title:
--   Restricted Tensor: is Smooth comp single Hom
-- statement:
--   The Restricted Tensor construction uses the is Smooth comp single Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L118-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Existence.lean#L118-L124

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Places
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Filter Function Module Set PiTensorProduct
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {V : Type u} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}

theorem GroundTheory.Automorphic.RestrictedTensor.isSmooth_comp_singleHom [DecidableEq ι] (hρ : IsSmooth ρ) (v : ι) :
    IsSmooth (ρ.comp (singleHom K v)) := by sorry
