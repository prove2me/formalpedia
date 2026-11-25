-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_eq_of_le_of_cellHeight_le
-- name    : GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le_of_cellHeight_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:55.635303+00:00
-- url     : https://prove2.me/theorems/7ba2e5ce-3f17-41bc-93ab-05aa29f4db1b
-- title:
--   Parabolic: cell Rank eq of le of cell Height le
-- statement:
--   The Parabolic construction uses the cell Rank eq of le of cell Height le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L400-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L400-L414

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}

theorem GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le_of_cellHeight_le {g x : GL (Fin n) F}
    (h : ∀ a b, cellRank β γ x a b ≤ cellRank β γ g a b)
    (hh : cellHeight β γ g ≤ cellHeight β γ x) : ∀ a b, cellRank β γ x a b = cellRank β γ g a b := by sorry
