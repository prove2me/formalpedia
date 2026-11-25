-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mul_e_diag_of_not_hasUpper
-- name    : GroundTheory.Automorphic.HarishChandra.canon_mul_e_diag_of_not_hasUpper
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:51.358181+00:00
-- url     : https://prove2.me/theorems/8b36cbe2-bf6a-41b8-9266-79262eb73c01
-- title:
--   Harish Chandra: canon mul e diag of not has Upper
-- statement:
--   The Harish Chandra construction uses the canon mul e diag of not has Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L84-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L84-L102

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
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

theorem GroundTheory.Automorphic.HarishChandra.canon_mul_e_diag_of_not_hasUpper {m : Fin n × Fin n →₀ ℕ} (h : ¬ HasUpper m) (k : Fin n) :
    canon m * e (k, k) = canon (m + Finsupp.single (k, k) 1) := by sorry
