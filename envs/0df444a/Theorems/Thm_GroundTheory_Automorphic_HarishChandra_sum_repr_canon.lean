-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_repr_canon
-- name    : GroundTheory.Automorphic.HarishChandra.sum_repr_canon
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:36.790806+00:00
-- url     : https://prove2.me/theorems/df032d0b-bb98-4ea5-a30b-e045466ada76
-- title:
--   Harish Chandra: sum repr canon
-- statement:
--   The Harish Chandra construction uses the sum repr canon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/ConstantCoeffRhoOneCanonMonomial.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/ConstantCoeffRhoOneCanonMonomial.lean#L88-L92

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
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

theorem GroundTheory.Automorphic.HarishChandra.sum_repr_canon (u : U n) :
    ∑ m ∈ (pbw.repr u).support, pbw.repr u m • canon m = u := by sorry
