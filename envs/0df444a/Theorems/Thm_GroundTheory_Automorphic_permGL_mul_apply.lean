-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_permGL_mul_apply
-- name    : GroundTheory.Automorphic.permGL_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:55.236208+00:00
-- url     : https://prove2.me/theorems/119eef20-bfa2-4701-b04f-e08429b9d33a
-- title:
--   Automorphic: perm GL mul apply
-- statement:
--   The Automorphic construction uses the perm GL mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L45-L52

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

theorem GroundTheory.Automorphic.permGL_mul_apply (M : Matrix (Fin n) (Fin n) k) (σ : Equiv.Perm (Fin n)) (r c : Fin n) :
    ((permGL k σ : Matrix (Fin n) (Fin n) k) * M) r c = M (σ⁻¹ r) c := by sorry
