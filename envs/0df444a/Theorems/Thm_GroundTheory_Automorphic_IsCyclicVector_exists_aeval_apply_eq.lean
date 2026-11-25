-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsCyclicVector_exists_aeval_apply_eq
-- name    : GroundTheory.Automorphic.IsCyclicVector.exists_aeval_apply_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:02.23788+00:00
-- url     : https://prove2.me/theorems/cbc71f4a-4dc8-4bdc-9c9a-56f584f7d1f4
-- title:
--   Is Cyclic Vector: exists aeval apply eq
-- statement:
--   The Is Cyclic Vector construction uses the exists aeval apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L188-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L188-L194

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

theorem GroundTheory.Automorphic.IsCyclicVector.exists_aeval_apply_eq (hv : IsCyclicVector f v) (x : V) :
    ∃ p : E[X], aeval f p v = x := by sorry
