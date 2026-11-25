-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_monomial_mem_geDeg
-- name    : GroundTheory.Automorphic.HarishChandra.rowOp_monomial_mem_geDeg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:01.568272+00:00
-- url     : https://prove2.me/theorems/244dbed3-e314-4d32-8c0b-ade0720ae088
-- title:
--   Harish Chandra: row Op monomial mem ge Deg
-- statement:
--   The Harish Chandra construction uses the row Op monomial mem ge Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L246-L251

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

theorem GroundTheory.Automorphic.HarishChandra.rowOp_monomial_mem_geDeg {t : ℕ} (i j : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ)
    (h : t ≤ s.degree) : rowOp i j (monomial s c) ∈ geDeg t := by sorry
