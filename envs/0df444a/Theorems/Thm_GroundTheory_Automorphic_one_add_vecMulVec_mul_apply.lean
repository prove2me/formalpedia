-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_one_add_vecMulVec_mul_apply
-- name    : GroundTheory.Automorphic.one_add_vecMulVec_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:21.396857+00:00
-- url     : https://prove2.me/theorems/1c4b5334-ed43-4ed0-ac49-50323e35ca2f
-- title:
--   Automorphic: one add vec Mul Vec mul apply
-- statement:
--   The Automorphic construction uses the one add vec Mul Vec mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L78-L81

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

theorem GroundTheory.Automorphic.one_add_vecMulVec_mul_apply (M : Matrix (Fin n) (Fin n) k) (i : Fin n) (u : Fin n → k)
    (r c : Fin n) :
    ((1 + vecMulVec u (Pi.single i 1)) * M) r c = M r c + u r * M i c := by sorry
