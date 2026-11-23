-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_zero_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:47.245605+00:00
-- url     : https://prove2.me/theorems/4f4fde47-de71-4d15-a1b8-cd27fcd6924b
-- title:
--   Harish Chandra: fischer zero right
-- statement:
--   The Harish Chandra construction uses the fischer zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L61-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L61-L61

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

theorem GroundTheory.Automorphic.HarishChandra.fischer_zero_right (f : MvPolynomial σ ℂ) : fischer f 0 = 0 := by sorry
