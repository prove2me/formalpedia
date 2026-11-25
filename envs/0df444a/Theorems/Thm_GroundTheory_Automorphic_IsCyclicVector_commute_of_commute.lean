-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsCyclicVector_commute_of_commute
-- name    : GroundTheory.Automorphic.IsCyclicVector.commute_of_commute
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:40.032687+00:00
-- url     : https://prove2.me/theorems/dd8ad11e-1160-4dad-823b-97287f87f708
-- title:
--   Is Cyclic Vector: commute of commute
-- statement:
--   The Is Cyclic Vector construction uses the commute of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L204-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L204-L208

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

theorem GroundTheory.Automorphic.IsCyclicVector.commute_of_commute (hv : IsCyclicVector f v) {g g' : Module.End E V}
    (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by sorry
