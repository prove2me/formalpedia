-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
-- name    : GroundTheory.Automorphic.HarishChandra.pbw_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:40.200371+00:00
-- url     : https://prove2.me/theorems/ebae3dc3-1ed5-4110-b116-e15cd5a83865
-- title:
--   Harish Chandra: pbw apply
-- statement:
--   The Harish Chandra construction uses the pbw apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/ConstantCoeffRhoOneCanonMonomial.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/ConstantCoeffRhoOneCanonMonomial.lean#L85-L86

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

theorem GroundTheory.Automorphic.HarishChandra.pbw_apply (m : Fin n × Fin n →₀ ℕ) : pbw (n := n) m = canon m := by sorry
