-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_GoodPiece_smul
-- name    : GroundTheory.Automorphic.Whittaker.GoodPiece.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:27.68306+00:00
-- url     : https://prove2.me/theorems/07c4bf64-af2e-4310-bbe3-1e064b0808e5
-- title:
--   Good Piece: smul
-- statement:
--   The Good Piece construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L278-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L278-L291

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
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [T2Space X]

theorem GroundTheory.Automorphic.Whittaker.GoodPiece.smul (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W) {A : Set X}
    (hA : GoodPiece (H := H) U C x₀ W A) (h : H) : GoodPiece (H := H) U C x₀ W (h • A) := by sorry
