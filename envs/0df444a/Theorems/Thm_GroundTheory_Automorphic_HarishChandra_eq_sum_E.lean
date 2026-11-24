-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eq_sum_E
-- name    : GroundTheory.Automorphic.HarishChandra.eq_sum_E
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:59.786923+00:00
-- url     : https://prove2.me/theorems/a7ff4b68-5250-4b23-8c4b-e049c2362853
-- title:
--   Harish Chandra: eq sum E
-- statement:
--   The Harish Chandra construction uses the eq sum E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L54-L59

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

theorem GroundTheory.Automorphic.HarishChandra.eq_sum_E (X : gl n) : X = ∑ a : Fin n × Fin n, X a.1 a.2 • E a := by sorry
