-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_setOf_le_cellRank
-- name    : GroundTheory.Automorphic.Parabolic.isOpen_setOf_le_cellRank
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:30.060134+00:00
-- url     : https://prove2.me/theorems/759d0b13-2a2e-4413-ad96-6577f5ac43e7
-- title:
--   Parabolic: is Open set Of le cell Rank
-- statement:
--   The Parabolic construction uses the is Open set Of le cell Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L418-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L418-L420

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
variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]

theorem GroundTheory.Automorphic.Parabolic.isOpen_setOf_le_cellRank (a b k : ℕ) :
    IsOpen {x : GL (Fin n) F | k ≤ cellRank β γ x a b} := by sorry
