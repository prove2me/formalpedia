-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_E_mul_sub_mul__63bac1
-- name    : GroundTheory.Automorphic.HarishChandra.E_mul_sub_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:51.066062+00:00
-- url     : https://prove2.me/theorems/63bac1c5-7941-439e-8034-a4c83449b9f9
-- title:
--   Harish Chandra: E mul sub mul
-- statement:
--   The Harish Chandra construction uses the E mul sub mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L30-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L30-L42

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
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
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.E_mul_sub_mul (a b : Fin n × Fin n) :
    E a * E b - E b * E a =
      (if a.2 = b.1 then E (a.1, b.2) else 0) - (if b.2 = a.1 then E (b.1, a.2) else 0) := by sorry
