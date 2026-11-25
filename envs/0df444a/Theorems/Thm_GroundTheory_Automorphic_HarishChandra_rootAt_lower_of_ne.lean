-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rootAt_lower_of_ne
-- name    : GroundTheory.Automorphic.HarishChandra.rootAt_lower_of_ne
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:06.066261+00:00
-- url     : https://prove2.me/theorems/e28ded8b-1d9f-43d1-ab42-2d2416896d2b
-- title:
--   Harish Chandra: root At lower of ne
-- statement:
--   The Harish Chandra construction uses the root At lower of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L238-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L238-L239

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

theorem GroundTheory.Automorphic.HarishChandra.rootAt_lower_of_ne {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) : rootAt (j, i) k = 0 := by sorry
