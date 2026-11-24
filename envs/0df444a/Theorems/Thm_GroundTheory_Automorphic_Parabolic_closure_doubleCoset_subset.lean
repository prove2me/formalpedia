-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_closure_doubleCoset_subset
-- name    : GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:44:31.007693+00:00
-- url     : https://prove2.me/theorems/4f090a41-49f7-47c6-92bb-bdf709891562
-- title:
--   Parabolic: closure double Coset subset
-- statement:
--   The Parabolic construction uses the closure double Coset subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L422-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L422-L441

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

theorem GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset (g : GL (Fin n) F) :
    closure (doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ⊆
      doubleCoset g (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) ∪
        {x | cellHeight β γ x < cellHeight β γ g} := by sorry
