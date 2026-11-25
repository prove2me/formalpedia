-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
-- name    : GroundTheory.Automorphic.HarishChandra.diagExp_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:58.100473+00:00
-- url     : https://prove2.me/theorems/420c1f77-339d-46d3-805b-303548c12e7a
-- title:
--   Harish Chandra: diag Exp apply
-- statement:
--   The Harish Chandra construction uses the diag Exp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L153-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L153-L153

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

theorem GroundTheory.Automorphic.HarishChandra.diagExp_apply (m : Fin n × Fin n →₀ ℕ) (i : Fin n) : diagExp m i = m (i, i) := by sorry

attribute [defeq] GroundTheory.Automorphic.HarishChandra.diagExp_apply
