-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_iUnion_doubleCoset_permGL
-- name    : GroundTheory.Automorphic.iUnion_doubleCoset_permGL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:56.602474+00:00
-- url     : https://prove2.me/theorems/8ab80c34-c495-5e4f-b6e4-ec93a822267a
-- title:
--   Automorphic: i Union double Coset perm GL
-- statement:
--   The Automorphic construction uses the i Union double Coset perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L327-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L327-L329

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

theorem GroundTheory.Automorphic.iUnion_doubleCoset_permGL :
    ⋃ σ : Equiv.Perm (Fin n), doubleCoset (permGL k σ) (borel n k) (borel n k) = Set.univ := by sorry
