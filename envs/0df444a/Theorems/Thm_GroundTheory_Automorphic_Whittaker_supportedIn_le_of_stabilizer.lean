-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_stabilizer
-- name    : GroundTheory.Automorphic.Whittaker.supportedIn_le_of_stabilizer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:02.317653+00:00
-- url     : https://prove2.me/theorems/3976f745-ef05-4787-b633-c3d08156711f
-- title:
--   Whittaker: supported In le of stabilizer
-- statement:
--   The Whittaker construction uses the supported In le of stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L588-L626
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L588-L626

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

theorem GroundTheory.Automorphic.Whittaker.supportedIn_le_of_stabilizer {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    (hχ : ∃ L : Subgroup H, IsOpen (L : Set H) ∧ ∀ l ∈ L, χ l = 1)
    {S₀ : Subgroup H} (hS₀ : IsCompact (S₀ : Set H)) {s : H} (hs : s ∈ S₀) (hsx : s • x₀ = x₀)
    (hχs : χ s ≠ 1) :
    supportedIn U ≤ relSpan χ U ⊔ (supportedIn U ⊓ vanishingOn C) := by sorry
