-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_mem_geDeg
-- name    : GroundTheory.Automorphic.HarishChandra.iterPd_mem_geDeg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:38.115002+00:00
-- url     : https://prove2.me/theorems/aa26e8d6-c15a-40c4-af73-3ecd2115c02e
-- title:
--   Harish Chandra: iter Pd mem ge Deg
-- statement:
--   The Harish Chandra construction uses the iter Pd mem ge Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L268-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L268-L274

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

theorem GroundTheory.Automorphic.HarishChandra.iterPd_mem_geDeg (w : List (Fin n × Fin n)) {t : ℕ} {f : Poly n} (hf : f ∈ geDeg t) :
    iterPd w f ∈ geDeg (t - w.length) := by sorry
