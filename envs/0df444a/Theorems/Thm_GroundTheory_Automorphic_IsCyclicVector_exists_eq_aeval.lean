-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsCyclicVector_exists_eq_aeval
-- name    : GroundTheory.Automorphic.IsCyclicVector.exists_eq_aeval
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:49.573228+00:00
-- url     : https://prove2.me/theorems/5e3885f9-16d4-42f4-be78-9725854d6833
-- title:
--   Is Cyclic Vector: exists eq aeval
-- statement:
--   The Is Cyclic Vector construction uses the exists eq aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L196-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L196-L202

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

theorem GroundTheory.Automorphic.IsCyclicVector.exists_eq_aeval (hv : IsCyclicVector f v) {g : Module.End E V}
    (hg : Commute f g) : ∃ p : E[X], g = aeval f p := by sorry
