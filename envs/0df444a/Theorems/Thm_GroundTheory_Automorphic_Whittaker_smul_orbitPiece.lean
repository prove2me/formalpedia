-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_smul_orbitPiece
-- name    : GroundTheory.Automorphic.Whittaker.smul_orbitPiece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:20.113659+00:00
-- url     : https://prove2.me/theorems/c21e9238-d0fc-48a4-a3f9-b1b925652078
-- title:
--   Whittaker: smul orbit Piece
-- statement:
--   The Whittaker construction uses the smul orbit Piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L142-L151

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

theorem GroundTheory.Automorphic.Whittaker.smul_orbitPiece {A : Subgroup H} {j : H} (hj : ∀ a ∈ A, j * a * j⁻¹ ∈ A)
    (hj' : ∀ a ∈ A, j⁻¹ * a * j ∈ A) (y : X) : j • orbitPiece A y = orbitPiece A (j • y) := by sorry
