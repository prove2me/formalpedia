-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rootAt_lower_other
-- name    : GroundTheory.Automorphic.HarishChandra.rootAt_lower_other
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:54:01.588963+00:00
-- url     : https://prove2.me/theorems/cf05d97f-76b1-5f4e-aeba-93c7c81349c0
-- title:
--   Harish Chandra: root At lower other
-- statement:
--   The Harish Chandra construction uses the root At lower other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L235-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L235-L236

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

theorem GroundTheory.Automorphic.HarishChandra.rootAt_lower_other (hij : i ≠ j) : rootAt (j, i) j = 1 := by sorry
