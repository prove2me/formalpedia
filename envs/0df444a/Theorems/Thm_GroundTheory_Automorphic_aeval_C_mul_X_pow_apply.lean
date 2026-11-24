-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_aeval_C_mul_X_pow_apply
-- name    : GroundTheory.Automorphic.aeval_C_mul_X_pow_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:40.557274+00:00
-- url     : https://prove2.me/theorems/b9ec6409-8fc8-4dd6-a15d-57364176423c
-- title:
--   Automorphic: aeval C mul X pow apply
-- statement:
--   The Automorphic construction uses the aeval C mul X pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L184-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L184-L186

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
variable {f : Module.End E V} {v : V}
omit [FiniteDimensional E V]

theorem GroundTheory.Automorphic.aeval_C_mul_X_pow_apply (f : Module.End E V) (a : E) (k : ℕ) (x : V) :
    aeval f (C a * X ^ k) x = a • (f ^ k) x := by sorry
