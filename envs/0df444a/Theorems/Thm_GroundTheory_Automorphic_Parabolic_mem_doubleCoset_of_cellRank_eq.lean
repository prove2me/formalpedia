-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_doubleCoset_of_cellRank_eq
-- name    : GroundTheory.Automorphic.Parabolic.mem_doubleCoset_of_cellRank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:06.517803+00:00
-- url     : https://prove2.me/theorems/f79c2a74-441e-47cf-95d1-10162f35bc1a
-- title:
--   Parabolic: mem double Coset of cell Rank eq
-- statement:
--   The Parabolic construction uses the mem double Coset of cell Rank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L343-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L343-L355

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

theorem GroundTheory.Automorphic.Parabolic.mem_doubleCoset_of_cellRank_eq {g x : GL (Fin n) F}
    (h : ∀ a b, cellRank β γ x a b = cellRank β γ g a b) :
    x ∈ doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) := by sorry
