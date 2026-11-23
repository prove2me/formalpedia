-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mul_one_add_vecMulVec_apply
-- name    : GroundTheory.Automorphic.mul_one_add_vecMulVec_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:27.022511+00:00
-- url     : https://prove2.me/theorems/068dbea8-063b-47e0-8b39-f4750f545b76
-- title:
--   Automorphic: mul one add vec Mul Vec apply
-- statement:
--   The Automorphic construction uses the mul one add vec Mul Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L73-L76

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

theorem GroundTheory.Automorphic.mul_one_add_vecMulVec_apply (M : Matrix (Fin n) (Fin n) k) (j : Fin n) (v : Fin n → k)
    (r c : Fin n) :
    (M * (1 + vecMulVec (Pi.single j 1) v)) r c = M r c + M r j * v c := by sorry
