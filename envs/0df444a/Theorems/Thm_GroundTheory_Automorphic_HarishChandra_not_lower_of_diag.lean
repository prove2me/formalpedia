-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_lower_of_diag
-- name    : GroundTheory.Automorphic.HarishChandra.not_lower_of_diag
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:07:31.78651+00:00
-- url     : https://prove2.me/theorems/b3296ce1-af4e-485f-99b5-e5a1fd3950da
-- title:
--   Harish Chandra: not lower of diag
-- statement:
--   The Harish Chandra construction uses the not lower of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L251-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L251-L252

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

theorem GroundTheory.Automorphic.HarishChandra.not_lower_of_diag {a : Fin n × Fin n} (h : IsDiag a) : ¬ IsLower a := by sorry
