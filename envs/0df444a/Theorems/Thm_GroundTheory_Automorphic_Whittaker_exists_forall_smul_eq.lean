-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_forall_smul_eq
-- name    : GroundTheory.Automorphic.Whittaker.exists_forall_smul_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:53.779803+00:00
-- url     : https://prove2.me/theorems/76c1d086-be4d-468c-98d2-cfb5692cd461
-- title:
--   Whittaker: exists forall smul eq
-- statement:
--   The Whittaker construction uses the exists forall smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L419-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L419-L448

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
omit [TotallyDisconnectedSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace H]

theorem GroundTheory.Automorphic.Whittaker.exists_forall_smul_eq {U C : Set X} (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) {f : X → ℂ} (hf : f ∈ supportedIn U) :
    ∃ L : Subgroup H, IsCompact (L : Set H) ∧ IsOpen (L : Set H) ∧
      ∀ l ∈ L, ∀ x ∈ orbit H x₀, f (l • x) = f x := by sorry
