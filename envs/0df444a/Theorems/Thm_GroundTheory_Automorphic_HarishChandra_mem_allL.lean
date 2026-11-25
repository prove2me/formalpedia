-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_allL
-- name    : GroundTheory.Automorphic.HarishChandra.mem_allL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:09.796781+00:00
-- url     : https://prove2.me/theorems/4dd9e46f-239b-4e28-916a-5f7ef2d994a0
-- title:
--   Harish Chandra: mem all L
-- statement:
--   The Harish Chandra construction uses the mem all L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L27-L29

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

theorem GroundTheory.Automorphic.HarishChandra.mem_allL (a : Fin n × Fin n) : a ∈ allL n := by sorry
