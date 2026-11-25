-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pderiv_monomial_mem_geDeg
-- name    : GroundTheory.Automorphic.HarishChandra.pderiv_monomial_mem_geDeg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:19.386976+00:00
-- url     : https://prove2.me/theorems/171760d5-b0a2-4f35-b7ae-a7a11e30c41f
-- title:
--   Harish Chandra: pderiv monomial mem ge Deg
-- statement:
--   The Harish Chandra construction uses the pderiv monomial mem ge Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L208-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L208-L215

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

theorem GroundTheory.Automorphic.HarishChandra.pderiv_monomial_mem_geDeg {t : ℕ} (a : Fin n × Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ)
    (h : t ≤ s.degree) : pderiv a (monomial s c : Poly n) ∈ geDeg (t - 1) := by sorry
