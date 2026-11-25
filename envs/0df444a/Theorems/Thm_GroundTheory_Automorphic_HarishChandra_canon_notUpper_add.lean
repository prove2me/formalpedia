-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_notUpper_add
-- name    : GroundTheory.Automorphic.HarishChandra.canon_notUpper_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:08:14.687481+00:00
-- url     : https://prove2.me/theorems/a50fc55e-06d4-4d8f-9ce2-9fc5e08b48f6
-- title:
--   Harish Chandra: canon not Upper add
-- statement:
--   The Harish Chandra construction uses the canon not Upper add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L254-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L254-L271

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

theorem GroundTheory.Automorphic.HarishChandra.canon_notUpper_add {m m' : Fin n × Fin n →₀ ℕ} (hm' : ∀ a ∈ m'.support, IsUpper a) :
    word (blockW (lowL n) m) * word (blockW (diagL n) m) * canon m' = canon (notUpper m + m') := by sorry
