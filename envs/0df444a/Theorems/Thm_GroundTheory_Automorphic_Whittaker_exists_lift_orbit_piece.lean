-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_lift_orbit_piece
-- name    : GroundTheory.Automorphic.Whittaker.exists_lift_orbit_piece
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:08.635003+00:00
-- url     : https://prove2.me/theorems/fad62b3f-02c4-485f-bdd4-a567d81b9bfd
-- title:
--   Whittaker: exists lift orbit piece
-- statement:
--   The Whittaker construction uses the exists lift orbit piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L218-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L218-L224

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
omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

theorem GroundTheory.Automorphic.Whittaker.exists_lift_orbit_piece {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) {L : Subgroup H} (hLc : IsCompact (L : Set H))
    (hLo : IsOpen (L : Set H)) {y : X} (hy : y ∈ orbit H x₀) :
    ∃ f ∈ supportedIn U, ∀ x ∈ orbit H x₀, f x = (orbitPiece L y).indicator 1 x := by sorry
