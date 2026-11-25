-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_eq_blocks
-- name    : GroundTheory.Automorphic.HarishChandra.expand_eq_blocks
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:07:49.77259+00:00
-- url     : https://prove2.me/theorems/224a3380-e1af-4cb9-be0f-2de9d6eb1054
-- title:
--   Harish Chandra: expand eq blocks
-- statement:
--   The Harish Chandra construction uses the expand eq blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L54-L56

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

theorem GroundTheory.Automorphic.HarishChandra.expand_eq_blocks (m : Fin n × Fin n →₀ ℕ) :
    expand m = blockW (lowL n) m ++ blockW (diagL n) m ++ blockW (upL n) m := by sorry
