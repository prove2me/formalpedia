-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_mul_mul
-- name    : GroundTheory.Automorphic.Parabolic.cellRank_mul_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:54.839536+00:00
-- url     : https://prove2.me/theorems/4169dc19-f1ff-4fb4-a6cb-1b70f9f91f44
-- title:
--   Parabolic: cell Rank mul mul
-- statement:
--   The Parabolic construction uses the cell Rank mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L141-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L141-L149

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

theorem GroundTheory.Automorphic.Parabolic.cellRank_mul_mul {p q : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hq : q ∈ blockUpper F n γ) (g : GL (Fin n) F) (a b : ℕ) :
    cellRank β γ (p * g * q) a b = cellRank β γ g a b := by sorry
