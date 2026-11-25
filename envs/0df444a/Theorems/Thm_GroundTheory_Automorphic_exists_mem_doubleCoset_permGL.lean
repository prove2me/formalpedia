-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_mem_doubleCoset_permGL
-- name    : GroundTheory.Automorphic.exists_mem_doubleCoset_permGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:20.005028+00:00
-- url     : https://prove2.me/theorems/053db390-b274-4987-8a84-755ba676e72f
-- title:
--   Automorphic: exists mem double Coset perm GL
-- statement:
--   The Automorphic construction uses the exists mem double Coset perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L262-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L262-L287

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

theorem GroundTheory.Automorphic.exists_mem_doubleCoset_permGL (g : GL (Fin n) k) :
    ∃ σ : Equiv.Perm (Fin n), g ∈ doubleCoset (permGL k σ) (borel n k) (borel n k) := by sorry
