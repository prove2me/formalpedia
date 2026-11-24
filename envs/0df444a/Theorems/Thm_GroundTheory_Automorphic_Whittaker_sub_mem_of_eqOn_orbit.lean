-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_of_eqOn_orbit
-- name    : GroundTheory.Automorphic.Whittaker.sub_mem_of_eqOn_orbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:45.183798+00:00
-- url     : https://prove2.me/theorems/87ce4a53-7e04-4dfd-bdb1-8cbcb15cf8b7
-- title:
--   Whittaker: sub mem of eq On orbit
-- statement:
--   The Whittaker construction uses the sub mem of eq On orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L234-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L234-L243

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
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [ContinuousSMul H X] [T2Space X] [TopologicalSpace H]

theorem GroundTheory.Automorphic.Whittaker.sub_mem_of_eqOn_orbit (hO : U ∩ C = orbit H x₀) {f g : X → ℂ} (hf : f ∈ supportedIn U)
    (hg : g ∈ supportedIn U) (heq : ∀ x ∈ orbit H x₀, f x = g x) :
    f - g ∈ supportedIn U ⊓ vanishingOn C := by sorry
