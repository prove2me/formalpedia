-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_isDiagExp_or
-- name    : GroundTheory.Automorphic.HarishChandra.isDiagExp_or
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:25.455578+00:00
-- url     : https://prove2.me/theorems/c0df014a-8562-4ee2-94df-0150fd93e213
-- title:
--   Harish Chandra: is Diag Exp or
-- statement:
--   The Harish Chandra construction uses the is Diag Exp or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L97-L104

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

theorem GroundTheory.Automorphic.HarishChandra.isDiagExp_or (m : Fin n × Fin n →₀ ℕ) : IsDiagExp m ∨ HasUpper m ∨ HasLower m := by sorry
