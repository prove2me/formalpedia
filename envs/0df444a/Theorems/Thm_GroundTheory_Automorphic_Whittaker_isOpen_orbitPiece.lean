-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isOpen_orbitPiece
-- name    : GroundTheory.Automorphic.Whittaker.isOpen_orbitPiece
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:56.171399+00:00
-- url     : https://prove2.me/theorems/e7612288-922f-4376-a1bb-ad70ed34d96c
-- title:
--   Whittaker: is Open orbit Piece
-- statement:
--   The Whittaker construction uses the is Open orbit Piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L201-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L201-L214

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
omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [TotallyDisconnectedSpace X]

theorem GroundTheory.Automorphic.Whittaker.isOpen_orbitPiece {x₀ : X} (hO : IsLocallyClosed (orbit H x₀)) {L : Subgroup H}
    (hLo : IsOpen (L : Set H)) {y : X} (hy : y ∈ orbit H x₀) :
    IsOpen ((Subtype.val : orbit H x₀ → X) ⁻¹' orbitPiece L y) := by sorry
