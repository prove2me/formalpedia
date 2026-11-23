-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_degree_sub_single
-- name    : GroundTheory.Automorphic.HarishChandra.degree_sub_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:25.096604+00:00
-- url     : https://prove2.me/theorems/e1c18b60-4b9c-43f7-a0af-1f96a9c8f719
-- title:
--   Harish Chandra: degree sub single
-- statement:
--   The Harish Chandra construction uses the degree sub single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L201-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L201-L206

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

theorem GroundTheory.Automorphic.HarishChandra.degree_sub_single {s : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n} (h : s a ≠ 0) :
    (s - Finsupp.single a 1).degree + 1 = s.degree := by sorry
