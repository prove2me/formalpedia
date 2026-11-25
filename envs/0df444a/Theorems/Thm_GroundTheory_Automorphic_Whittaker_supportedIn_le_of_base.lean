-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_base
-- name    : GroundTheory.Automorphic.Whittaker.supportedIn_le_of_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:21.146823+00:00
-- url     : https://prove2.me/theorems/d22969aa-e65c-4892-bf1d-fcdd84de8a59
-- title:
--   Whittaker: supported In le of base
-- statement:
--   The Whittaker construction uses the supported In le of base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L450-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L450-L586

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
variable {U C : Set X} {x₀ : X}

theorem GroundTheory.Automorphic.Whittaker.supportedIn_le_of_base {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W)
    (L₀ : Subgroup H) (hL₀c : IsCompact (L₀ : Set H)) (hL₀o : IsOpen (L₀ : Set H))
    (hχL₀ : ∀ l ∈ L₀, χ l = 1) (f₀ : X → ℂ)
    (hf₀O : ∀ x ∈ orbit H x₀, f₀ x = (orbitPiece L₀ x₀).indicator 1 x)
    (hbase : f₀ ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)) :
    supportedIn U ≤ W ⊔ (supportedIn U ⊓ vanishingOn C) := by sorry
