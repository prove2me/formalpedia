-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_self_eq_zero_iff
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_self_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:34.558613+00:00
-- url     : https://prove2.me/theorems/22f513c2-591c-46a1-b8e7-1b2070148321
-- title:
--   Harish Chandra: fischer self eq zero iff
-- statement:
--   The Harish Chandra construction uses the fischer self eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L141-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L141-L153

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {σ : Type*}

theorem GroundTheory.Automorphic.HarishChandra.fischer_self_eq_zero_iff (f : MvPolynomial σ ℂ) : fischer f f = 0 ↔ f = 0 := by sorry
