-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_spanLower_le_nMinusU
-- name    : GroundTheory.Automorphic.HarishChandra.spanLower_le_nMinusU
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:11.318803+00:00
-- url     : https://prove2.me/theorems/daded81b-8dfe-52f9-8c8a-d6837bb327d2
-- title:
--   Harish Chandra: span Lower le n Minus U
-- statement:
--   The Harish Chandra construction uses the span Lower le n Minus U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L367-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L367-L368

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
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
open scoped IsMulCommutative

theorem GroundTheory.Automorphic.HarishChandra.spanLower_le_nMinusU : spanLower n ≤ nMinusU n := by sorry
