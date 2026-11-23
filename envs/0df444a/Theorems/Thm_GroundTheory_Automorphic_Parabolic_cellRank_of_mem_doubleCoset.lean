-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_of_mem_doubleCoset
-- name    : GroundTheory.Automorphic.Parabolic.cellRank_of_mem_doubleCoset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:56.543902+00:00
-- url     : https://prove2.me/theorems/9b25ad77-26e8-4e47-bf42-04f9a3026f6e
-- title:
--   Parabolic: cell Rank of mem double Coset
-- statement:
--   The Parabolic construction uses the cell Rank of mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L151-L155

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

theorem GroundTheory.Automorphic.Parabolic.cellRank_of_mem_doubleCoset {g x : GL (Fin n) F}
    (hx : x ∈ doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) (a b : ℕ) :
    cellRank β γ x a b = cellRank β γ g a b := by sorry
