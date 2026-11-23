-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_constantCoeff_eq_zero_of_mem_geDeg
-- name    : GroundTheory.Automorphic.HarishChandra.constantCoeff_eq_zero_of_mem_geDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:05.999601+00:00
-- url     : https://prove2.me/theorems/21470392-f045-4597-b94e-404610712334
-- title:
--   Harish Chandra: constant Coeff eq zero of mem ge Deg
-- statement:
--   The Harish Chandra construction uses the constant Coeff eq zero of mem ge Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L182-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L182-L186

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

theorem GroundTheory.Automorphic.HarishChandra.constantCoeff_eq_zero_of_mem_geDeg {f : Poly n} (hf : f ∈ geDeg 1) :
    constantCoeff f = 0 := by sorry
