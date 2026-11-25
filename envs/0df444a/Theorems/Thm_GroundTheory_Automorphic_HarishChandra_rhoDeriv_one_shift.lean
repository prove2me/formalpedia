-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rhoDeriv_one_shift
-- name    : GroundTheory.Automorphic.HarishChandra.rhoDeriv_one_shift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:20.05627+00:00
-- url     : https://prove2.me/theorems/e64214cc-1a55-425e-a79c-5d42d5cae9a9
-- title:
--   Harish Chandra: rho Deriv one shift
-- statement:
--   The Harish Chandra construction uses the rho Deriv one shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L138-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L138-L151

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

theorem GroundTheory.Automorphic.HarishChandra.rhoDeriv_one_shift (M : gl n) (f : Poly n) :
    rhoDeriv 1 M (shift f) = shift (rhoDeriv 0 M f) := by sorry
