-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_smul_right
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_smul_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:44.925661+00:00
-- url     : https://prove2.me/theorems/9a336783-2c65-4287-adc6-d621918e5f48
-- title:
--   Harish Chandra: fischer smul right
-- statement:
--   The Harish Chandra construction uses the fischer smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L53-L57

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

theorem GroundTheory.Automorphic.HarishChandra.fischer_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer f (c • g) = c * fischer f g := by sorry
