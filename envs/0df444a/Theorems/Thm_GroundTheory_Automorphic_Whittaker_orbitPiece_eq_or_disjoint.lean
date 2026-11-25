-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_orbitPiece_eq_or_disjoint
-- name    : GroundTheory.Automorphic.Whittaker.orbitPiece_eq_or_disjoint
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:49.653711+00:00
-- url     : https://prove2.me/theorems/1eddebcf-64b7-45c0-9ab3-583d0f67df18
-- title:
--   Whittaker: orbit Piece eq or disjoint
-- statement:
--   The Whittaker construction uses the orbit Piece eq or disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L131-L136

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
omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [ContinuousSMul H X]

theorem GroundTheory.Automorphic.Whittaker.orbitPiece_eq_or_disjoint (L : Subgroup H) (y z : X) :
    orbitPiece L y = orbitPiece L z ∨ Disjoint (orbitPiece L y) (orbitPiece L z) := by sorry
