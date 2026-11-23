-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_eq_of_permGL_mem_doubleCoset
-- name    : GroundTheory.Automorphic.eq_of_permGL_mem_doubleCoset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:07.773815+00:00
-- url     : https://prove2.me/theorems/55a5af09-956f-4e7c-97cd-35d03b5d5a5e
-- title:
--   Automorphic: eq of perm GL mem double Coset
-- statement:
--   The Automorphic construction uses the eq of perm GL mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L289-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L289-L310

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

theorem GroundTheory.Automorphic.eq_of_permGL_mem_doubleCoset {σ τ : Equiv.Perm (Fin n)}
    (h : permGL k τ ∈ doubleCoset (permGL k σ) (borel n k) (borel n k)) : σ = τ := by sorry
