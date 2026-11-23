-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_e_apply
-- name    : GroundTheory.Automorphic.HarishChandra.rho_e_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:43.386621+00:00
-- url     : https://prove2.me/theorems/f67ae3bf-de55-4892-b046-c5b7f124230d
-- title:
--   Harish Chandra: rho e apply
-- statement:
--   The Harish Chandra construction uses the rho e apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L68-L70

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

theorem GroundTheory.Automorphic.HarishChandra.rho_e_apply (c : Matrix (Fin n) (Fin n) ℂ) (a : Fin n × Fin n) (f : Poly n) :
    rho c (e a) f = rhoDeriv c (E a) f := by sorry
