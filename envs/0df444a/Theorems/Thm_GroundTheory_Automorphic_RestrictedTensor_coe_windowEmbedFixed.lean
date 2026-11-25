-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_coe_windowEmbedFixed
-- name    : GroundTheory.Automorphic.RestrictedTensor.coe_windowEmbedFixed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:56:27.158208+00:00
-- url     : https://prove2.me/theorems/5e4e2fb1-4526-4048-a65d-723f4b8a0b58
-- title:
--   Restricted Tensor: coe window Embed Fixed
-- statement:
--   The Restricted Tensor construction uses the coe window Embed Fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Irreducible.lean#L127-L130

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
omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc

theorem GroundTheory.Automorphic.RestrictedTensor.coe_windowEmbedFixed (t : ⨂[ℂ] v : S, fixedVectors (π v) (K' v)) :
    ((windowEmbedFixed hξ S hSK hSξ t : restrictedTensor ξ) : ⨂[ℂ] v, V v) =
      windowEmbed ξ S t := by sorry
