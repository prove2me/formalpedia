-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_permGL_injective
-- name    : GroundTheory.Automorphic.permGL_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:00.00613+00:00
-- url     : https://prove2.me/theorems/6d138d08-2c3a-4a66-b967-349320aad510
-- title:
--   Automorphic: perm GL injective
-- statement:
--   The Automorphic construction uses the perm GL injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L352-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L352-L356

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

theorem GroundTheory.Automorphic.permGL_injective : Function.Injective (permGL k : Equiv.Perm (Fin n) → GL (Fin n) k) := by sorry
