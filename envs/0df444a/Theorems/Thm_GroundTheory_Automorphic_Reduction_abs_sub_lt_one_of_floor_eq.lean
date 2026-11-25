-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_abs_sub_lt_one_of_floor_eq
-- name    : GroundTheory.Automorphic.Reduction.abs_sub_lt_one_of_floor_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:09.75487+00:00
-- url     : https://prove2.me/theorems/359c7e9c-03b7-40c6-b090-5d974bffc91a
-- title:
--   Reduction: abs sub lt one of floor eq
-- statement:
--   The Reduction construction uses the abs sub lt one of floor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L45-L53

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Automorphic.Reduction.abs_sub_lt_one_of_floor_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : ⌊x⌋₊ = ⌊y⌋₊) :
    |x - y| < 1 := by sorry
