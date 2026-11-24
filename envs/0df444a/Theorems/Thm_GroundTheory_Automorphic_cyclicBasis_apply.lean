-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_cyclicBasis_apply
-- name    : GroundTheory.Automorphic.cyclicBasis_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:42.539223+00:00
-- url     : https://prove2.me/theorems/ee7138d5-90d2-4d15-ac45-071e855d25f2
-- title:
--   Automorphic: cyclic Basis apply
-- statement:
--   The Automorphic construction uses the cyclic Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L179-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L179-L181

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

theorem GroundTheory.Automorphic.cyclicBasis_apply (hv : IsCyclicVector f v) (k : Fin (finrank E V)) :
    cyclicBasis hv k = (f ^ (k : ℕ)) v := by sorry
