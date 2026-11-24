-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_toFinsupp_map_swap_cons
-- name    : GroundTheory.Automorphic.HarishChandra.toFinsupp_map_swap_cons
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:58.941774+00:00
-- url     : https://prove2.me/theorems/bfb074b5-1edd-48a6-b8d0-dc5f7755278e
-- title:
--   Harish Chandra: to Finsupp map swap cons
-- statement:
--   The Harish Chandra construction uses the to Finsupp map swap cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L310-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L310-L316

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.toFinsupp_map_swap_cons (a : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Multiset.toFinsupp (((a :: w).map Prod.swap : List _) : Multiset (Fin n × Fin n)) =
      Finsupp.single (a.2, a.1) 1 +
        Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) := by sorry
