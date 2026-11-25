-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_permGL_mem_doubleCoset_of_card
-- name    : GroundTheory.Automorphic.Parabolic.permGL_mem_doubleCoset_of_card
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:56.327595+00:00
-- url     : https://prove2.me/theorems/5c3a9da1-055a-4467-861f-c876c625113b
-- title:
--   Parabolic: perm GL mem double Coset of card
-- statement:
--   The Parabolic construction uses the perm GL mem double Coset of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L217-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L217-L302

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

theorem GroundTheory.Automorphic.Parabolic.permGL_mem_doubleCoset_of_card {w w' : Equiv.Perm (Fin n)}
    (h : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card) :
    permGL F w' ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ) := by sorry
