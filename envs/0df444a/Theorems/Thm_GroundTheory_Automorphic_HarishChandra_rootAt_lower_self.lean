-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rootAt_lower_self
-- name    : GroundTheory.Automorphic.HarishChandra.rootAt_lower_self
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:54:17.163544+00:00
-- url     : https://prove2.me/theorems/447240ff-1785-5124-9ef2-25b36b6d2ca2
-- title:
--   Harish Chandra: root At lower self
-- statement:
--   The Harish Chandra construction uses the root At lower self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L232-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L232-L233

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
variable {i j : Fin n}

theorem GroundTheory.Automorphic.HarishChandra.rootAt_lower_self (hij : i ≠ j) : rootAt (j, i) i = -1 := by sorry
