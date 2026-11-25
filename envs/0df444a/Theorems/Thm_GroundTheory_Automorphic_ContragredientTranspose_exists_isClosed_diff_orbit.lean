-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_isClosed_diff_orbit
-- name    : GroundTheory.Automorphic.ContragredientTranspose.exists_isClosed_diff_orbit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:15.595151+00:00
-- url     : https://prove2.me/theorems/1e1414b3-1a34-4e2d-812e-36888b2a705a
-- title:
--   Contragredient Transpose: exists is Closed diff orbit
-- statement:
--   The Contragredient Transpose construction uses the exists is Closed diff orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L119-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L119-L178

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {H X : Type*} [Group H] [TopologicalSpace H] [SigmaCompactSpace H] [TopologicalSpace X]
  [T2Space X] [LocallyCompactSpace X] [MulAction H X] [ContinuousSMul H X]

theorem GroundTheory.Automorphic.ContragredientTranspose.exists_isClosed_diff_orbit {Z : Set X} (hZ : IsClosed Z) (hZne : Z.Nonempty)
    (hZinv : ∀ h : H, ∀ x ∈ Z, h • x ∈ Z) {s : Set X} (hs : s.Countable)
    (hcov : Z ⊆ ⋃ x ∈ s, orbit H x) :
    ∃ x₀ ∈ Z, IsClosed (Z \ orbit H x₀) := by sorry
