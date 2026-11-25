-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_upper_of_lower
-- name    : GroundTheory.Automorphic.HarishChandra.not_upper_of_lower
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:08:25.077455+00:00
-- url     : https://prove2.me/theorems/06142042-868d-4d6a-98b1-a0ac6a28bce3
-- title:
--   Harish Chandra: not upper of lower
-- statement:
--   The Harish Chandra construction uses the not upper of lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L242-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L242-L243

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

theorem GroundTheory.Automorphic.HarishChandra.not_upper_of_lower {a : Fin n × Fin n} (h : IsLower a) : ¬ IsUpper a := by sorry
