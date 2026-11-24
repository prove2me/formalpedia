-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellHeight_of_mem_doubleCoset
-- name    : GroundTheory.Automorphic.Parabolic.cellHeight_of_mem_doubleCoset
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:42.381062+00:00
-- url     : https://prove2.me/theorems/d06c430b-e5d8-44de-b443-ca781ab95714
-- title:
--   Parabolic: cell Height of mem double Coset
-- statement:
--   The Parabolic construction uses the cell Height of mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L445-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L445-L449

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
omit [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]

theorem GroundTheory.Automorphic.Parabolic.cellHeight_of_mem_doubleCoset {g x : GL (Fin n) F}
    (hx : x ∈ doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) :
    cellHeight β γ x = cellHeight β γ g := by sorry
