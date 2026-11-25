-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_GoodPiece_down
-- name    : GroundTheory.Automorphic.Whittaker.GoodPiece.down
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:01.538883+00:00
-- url     : https://prove2.me/theorems/059d636e-1675-4cf1-9326-e7ca59b75e6b
-- title:
--   Good Piece: down
-- statement:
--   The Good Piece construction uses the down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L377-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L377-L415

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
omit [TotallyDisconnectedSpace X] [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

theorem GroundTheory.Automorphic.Whittaker.GoodPiece.down {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hW : relSpan χ U ≤ W)
    {J A : Subgroup H} (hJc : IsCompact (J : Set H)) (hχJ : ∀ j ∈ J, χ j = 1)
    (hAo : IsOpen (A : Set H)) (hAJ : A ≤ J)
    (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) {y : X} (hy : y ∈ orbit H x₀)
    (hJ : GoodPiece (H := H) U C x₀ W (orbitPiece J y)) :
    GoodPiece (H := H) U C x₀ W (orbitPiece A y) := by sorry
