-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_permGL_mem_doubleCoset
-- name    : GroundTheory.Automorphic.Parabolic.exists_permGL_mem_doubleCoset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:27.494385+00:00
-- url     : https://prove2.me/theorems/8b4fa2e3-3c7c-4cbe-88f0-a67f73edcff8
-- title:
--   Parabolic: exists perm GL mem double Coset
-- statement:
--   The Parabolic construction uses the exists perm GL mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L322-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCells.lean#L322-L341

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

theorem GroundTheory.Automorphic.Parabolic.exists_permGL_mem_doubleCoset (g : GL (Fin n) F) :
    ∃ w : Equiv.Perm (Fin n), g ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ) := by sorry
