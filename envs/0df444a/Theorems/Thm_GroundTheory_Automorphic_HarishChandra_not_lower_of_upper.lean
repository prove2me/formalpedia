-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_lower_of_upper
-- name    : GroundTheory.Automorphic.HarishChandra.not_lower_of_upper
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:07:38.197484+00:00
-- url     : https://prove2.me/theorems/4f2b8d88-d0aa-4288-a509-37e99b64b59f
-- title:
--   Harish Chandra: not lower of upper
-- statement:
--   The Harish Chandra construction uses the not lower of upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L248-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L248-L249

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

theorem GroundTheory.Automorphic.HarishChandra.not_lower_of_upper {a : Fin n × Fin n} (h : IsUpper a) : ¬ IsLower a := by sorry
