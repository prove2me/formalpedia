-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_commute_of_commute_of_separable
-- name    : GroundTheory.Automorphic.commute_of_commute_of_separable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:48.215252+00:00
-- url     : https://prove2.me/theorems/1d81cfe2-a051-4920-8e9e-ac96a141a4b7
-- title:
--   Automorphic: commute of commute of separable
-- statement:
--   The Automorphic construction uses the commute of commute of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L255-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean#L255-L258

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

theorem GroundTheory.Automorphic.commute_of_commute_of_separable [Infinite E] {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by sorry
