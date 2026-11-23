-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_geDeg_anti
-- name    : GroundTheory.Automorphic.HarishChandra.geDeg_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:05.46728+00:00
-- url     : https://prove2.me/theorems/a684ffbd-9e65-4586-b907-0e010c86d1c4
-- title:
--   Harish Chandra: ge Deg anti
-- statement:
--   The Harish Chandra construction uses the ge Deg anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L172-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L172-L173

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

theorem GroundTheory.Automorphic.HarishChandra.geDeg_anti {t t' : ℕ} (h : t' ≤ t) : (geDeg t : Submodule ℂ (Poly n)) ≤ geDeg t' := by sorry
