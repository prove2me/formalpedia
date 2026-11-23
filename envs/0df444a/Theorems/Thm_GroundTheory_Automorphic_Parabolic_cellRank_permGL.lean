-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_permGL
-- name    : GroundTheory.Automorphic.Parabolic.cellRank_permGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:21.199244+00:00
-- url     : https://prove2.me/theorems/f1037717-6999-4d48-8859-dc4a2656c35c
-- title:
--   Parabolic: cell Rank perm GL
-- statement:
--   The Parabolic construction uses the cell Rank perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L163-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L163-L206

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
variable {β γ : Fin n → ℕ}

theorem GroundTheory.Automorphic.Parabolic.cellRank_permGL (w : Equiv.Perm (Fin n)) (a b : ℕ) :
    cellRank β γ (permGL F w) a b = (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card := by sorry
