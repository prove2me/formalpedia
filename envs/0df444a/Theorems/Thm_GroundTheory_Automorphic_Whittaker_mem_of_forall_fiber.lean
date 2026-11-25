-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_of_forall_fiber
-- name    : GroundTheory.Automorphic.Whittaker.mem_of_forall_fiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:17.787122+00:00
-- url     : https://prove2.me/theorems/5bb2284b-8bd6-43d4-bac5-c495395c1844
-- title:
--   Whittaker: mem of forall fiber
-- statement:
--   The Whittaker construction uses the mem of forall fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L180-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L180-L258

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
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
open Set Topology
variable {X : Type*} [TopologicalSpace X]
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem GroundTheory.Automorphic.Whittaker.mem_of_forall_fiber {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] {U C : Set X} (hC : IsClosed C) {p : X → Y}
    (hp : Continuous p) {W : Submodule ℂ (X → ℂ)}
    (hWK : supportedIn U ⊓ vanishingOn C ≤ W)
    (hWmul : ∀ V : Set Y, IsClopen V → ∀ w ∈ W, (fun x => (p ⁻¹' V).indicator 1 x * w x) ∈ W)
    {g : X → ℂ} (hg : g ∈ supportedIn U)
    (hfib : ∀ y, g ∈ W ⊔ (supportedIn U ⊓ vanishingOn (C ∩ p ⁻¹' {y}))) : g ∈ W := by sorry
