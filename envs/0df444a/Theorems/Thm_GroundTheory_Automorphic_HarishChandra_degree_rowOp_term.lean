-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_degree_rowOp_term
-- name    : GroundTheory.Automorphic.HarishChandra.degree_rowOp_term
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:58.002152+00:00
-- url     : https://prove2.me/theorems/b3f6f2ed-d8b5-455c-b4ba-544bd9d565ac
-- title:
--   Harish Chandra: degree row Op term
-- statement:
--   The Harish Chandra construction uses the degree row Op term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L241-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L241-L244

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

theorem GroundTheory.Automorphic.HarishChandra.degree_rowOp_term {i j k : Fin n} {s : Fin n × Fin n →₀ ℕ} (hs : s (j, k) ≠ 0) :
    (Finsupp.single (i, k) 1 + (s - Finsupp.single (j, k) 1)).degree = s.degree := by sorry
