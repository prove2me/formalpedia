-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_isCyclicVector
-- name    : GroundTheory.Automorphic.exists_isCyclicVector
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:15.252849+00:00
-- url     : https://prove2.me/theorems/9d346446-fe80-491b-b43d-bcd7a3b89de7
-- title:
--   Automorphic: exists is Cyclic Vector
-- statement:
--   The Automorphic construction uses the exists is Cyclic Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L170-L172

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

theorem GroundTheory.Automorphic.exists_isCyclicVector [Infinite E] (f : Module.End E V) (hf : f.charpoly.Separable) :
    ∃ v, IsCyclicVector f v := by sorry
