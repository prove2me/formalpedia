-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_borel_diag_ne_zero
-- name    : GroundTheory.Automorphic.borel_diag_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:47.210566+00:00
-- url     : https://prove2.me/theorems/f9e46847-bac6-4f4f-9734-2da492ac43cc
-- title:
--   Automorphic: borel diag ne zero
-- statement:
--   The Automorphic construction uses the borel diag ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L54-L59

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

theorem GroundTheory.Automorphic.borel_diag_ne_zero {b : GL (Fin n) k} (hb : b ∈ borel n k) (i : Fin n) :
    (b : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by sorry
