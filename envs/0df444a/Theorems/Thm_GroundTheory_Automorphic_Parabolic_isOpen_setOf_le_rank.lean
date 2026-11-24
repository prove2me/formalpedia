-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_setOf_le_rank
-- name    : GroundTheory.Automorphic.Parabolic.isOpen_setOf_le_rank
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:08.80565+00:00
-- url     : https://prove2.me/theorems/0cbd91b9-d063-4c32-b4af-d5ae33a68af6
-- title:
--   Parabolic: is Open set Of le rank
-- statement:
--   The Parabolic construction uses the is Open set Of le rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L57-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L57-L75

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
variable {K : Type*} [Field K] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m]
variable [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]

theorem GroundTheory.Automorphic.Parabolic.isOpen_setOf_le_rank (k : ℕ) : IsOpen {A : Matrix m l K | k ≤ A.rank} := by sorry
