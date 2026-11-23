-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mul_permGL_apply
-- name    : GroundTheory.Automorphic.mul_permGL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:12.002025+00:00
-- url     : https://prove2.me/theorems/16613067-a4f5-4bf9-8fc5-1fe379c70f8b
-- title:
--   Automorphic: mul perm GL apply
-- statement:
--   The Automorphic construction uses the mul perm GL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L41-L43

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]

theorem GroundTheory.Automorphic.mul_permGL_apply (M : Matrix (Fin n) (Fin n) k) (σ : Equiv.Perm (Fin n)) (r c : Fin n) :
    (M * (permGL k σ : Matrix (Fin n) (Fin n) k)) r c = M r (σ c) := by sorry
