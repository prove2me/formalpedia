-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_monomial_mem_geDeg
-- name    : GroundTheory.Automorphic.HarishChandra.monomial_mem_geDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:24.890483+00:00
-- url     : https://prove2.me/theorems/34a8971e-0d5f-45d2-a089-f75180633f4d
-- title:
--   Harish Chandra: monomial mem ge Deg
-- statement:
--   The Harish Chandra construction uses the monomial mem ge Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L175-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L175-L180

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

theorem GroundTheory.Automorphic.HarishChandra.monomial_mem_geDeg {t : ℕ} (s : Fin n × Fin n →₀ ℕ) (c : ℂ) (h : t ≤ s.degree) :
    (monomial s c : Poly n) ∈ geDeg t := by sorry
