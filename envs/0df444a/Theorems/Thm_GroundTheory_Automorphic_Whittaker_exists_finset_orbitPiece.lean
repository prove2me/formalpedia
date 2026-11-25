-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_finset_orbitPiece
-- name    : GroundTheory.Automorphic.Whittaker.exists_finset_orbitPiece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:51.576829+00:00
-- url     : https://prove2.me/theorems/9206a672-1f30-4ea6-99ff-c038cf2ec664
-- title:
--   Whittaker: exists finset orbit Piece
-- statement:
--   The Whittaker construction uses the exists finset orbit Piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L295-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L295-L344

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

theorem GroundTheory.Automorphic.Whittaker.exists_finset_orbitPiece (hOl : IsLocallyClosed (orbit H x₀)) {J A : Subgroup H}
    (hJc : IsCompact (J : Set H)) (hAo : IsOpen (A : Set H)) (hAJ : A ≤ J)
    (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) {y : X} (hy : y ∈ orbit H x₀) :
    ∃ 𝒮 : Finset (Set X), 𝒮.Nonempty ∧ (∀ S ∈ 𝒮, ∃ j ∈ J, S = j • orbitPiece A y) ∧
      ∀ x, (orbitPiece J y).indicator (1 : X → ℂ) x = ∑ S ∈ 𝒮, S.indicator 1 x := by sorry
