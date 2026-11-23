-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pderiv_mem_geDeg
-- name    : GroundTheory.Automorphic.HarishChandra.pderiv_mem_geDeg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:28.508007+00:00
-- url     : https://prove2.me/theorems/4bfff4c9-860a-4fb1-9ecf-97a3cb902ee6
-- title:
--   Harish Chandra: pderiv mem ge Deg
-- statement:
--   The Harish Chandra construction uses the pderiv mem ge Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L217-L222

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

theorem GroundTheory.Automorphic.HarishChandra.pderiv_mem_geDeg {t : ℕ} (a : Fin n × Fin n) {f : Poly n} (hf : f ∈ geDeg t) :
    pderiv a f ∈ geDeg (t - 1) := by sorry
