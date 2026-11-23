-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
-- name    : GroundTheory.Automorphic.HarishChandra.iterPd_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:39.543323+00:00
-- url     : https://prove2.me/theorems/5cab9151-de12-4ec9-af02-a53ee3f459ce
-- title:
--   Harish Chandra: iter Pd cons
-- statement:
--   The Harish Chandra construction uses the iter Pd cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L265-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L265-L266

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

theorem GroundTheory.Automorphic.HarishChandra.iterPd_cons (a : Fin n × Fin n) (w : List (Fin n × Fin n)) (f : Poly n) :
    iterPd (a :: w) f = pderiv (a.2, a.1) (iterPd w f) := by sorry

attribute [defeq] GroundTheory.Automorphic.HarishChandra.iterPd_cons
