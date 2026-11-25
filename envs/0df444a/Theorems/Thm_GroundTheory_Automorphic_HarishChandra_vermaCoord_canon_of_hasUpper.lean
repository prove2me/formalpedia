-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_vermaCoord_canon_of_hasUpper
-- name    : GroundTheory.Automorphic.HarishChandra.vermaCoord_canon_of_hasUpper
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:35.282525+00:00
-- url     : https://prove2.me/theorems/8fde28c6-9e7d-55cd-8a27-f1eebdbf92bb
-- title:
--   Harish Chandra: verma Coord canon of has Upper
-- statement:
--   The Harish Chandra construction uses the verma Coord canon of has Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L63-L65

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

theorem GroundTheory.Automorphic.HarishChandra.vermaCoord_canon_of_hasUpper (lam : Fin n → ℂ) {m : Fin n × Fin n →₀ ℕ} (h : HasUpper m) :
    vermaCoord lam (canon m) = 0 := by sorry
