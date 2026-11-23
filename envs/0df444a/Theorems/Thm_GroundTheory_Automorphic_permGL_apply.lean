-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_permGL_apply
-- name    : GroundTheory.Automorphic.permGL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:21.633171+00:00
-- url     : https://prove2.me/theorems/d0619124-5e50-47d1-acf2-2d606fbcbf1f
-- title:
--   Automorphic: perm GL apply
-- statement:
--   The Automorphic construction uses the perm GL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L36-L39

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

theorem GroundTheory.Automorphic.permGL_apply (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (permGL k σ : Matrix (Fin n) (Fin n) k) i j = if i = σ j then 1 else 0 := by sorry
