-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_blockW_diagL
-- name    : GroundTheory.Automorphic.HarishChandra.word_blockW_diagL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:07:51.341319+00:00
-- url     : https://prove2.me/theorems/4b611d8f-6af5-4427-9951-20e564c6d1b9
-- title:
--   Harish Chandra: word block W diag L
-- statement:
--   The Harish Chandra construction uses the word block W diag L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L158-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L158-L184

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

theorem GroundTheory.Automorphic.HarishChandra.word_blockW_diagL (m : Fin n × Fin n →₀ ℕ) :
    word (blockW (diagL n) m) = hcEmb (monomial (diagExp m) 1) := by sorry
