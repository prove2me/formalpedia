-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_monomial
-- name    : GroundTheory.Automorphic.HarishChandra.rowOp_monomial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:44.162786+00:00
-- url     : https://prove2.me/theorems/098ff7a2-9e98-41f5-8ef4-7e4268b147b2
-- title:
--   Harish Chandra: row Op monomial
-- statement:
--   The Harish Chandra construction uses the row Op monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L224-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L224-L229

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

theorem GroundTheory.Automorphic.HarishChandra.rowOp_monomial (i j : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    rowOp i j (monomial s c) =
      ∑ k, monomial (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)) (c * s (j, k)) := by sorry
