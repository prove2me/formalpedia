-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_isDiagExp_of_hasUpper
-- name    : GroundTheory.Automorphic.HarishChandra.not_isDiagExp_of_hasUpper
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:26.216277+00:00
-- url     : https://prove2.me/theorems/c5a2b290-e945-4856-9578-b694942855dd
-- title:
--   Harish Chandra: not is Diag Exp of has Upper
-- statement:
--   The Harish Chandra construction uses the not is Diag Exp of has Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L106-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L106-L111

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

theorem GroundTheory.Automorphic.HarishChandra.not_isDiagExp_of_hasUpper {m : Fin n × Fin n →₀ ℕ} (h : HasUpper m) : ¬ IsDiagExp m := by sorry
