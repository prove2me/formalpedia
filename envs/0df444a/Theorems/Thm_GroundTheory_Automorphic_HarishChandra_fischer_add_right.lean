-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_add_right
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:54.743549+00:00
-- url     : https://prove2.me/theorems/5e9b63df-55dd-4f2f-b190-e39535a7ba8c
-- title:
--   Harish Chandra: fischer add right
-- statement:
--   The Harish Chandra construction uses the fischer add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L45-L51

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

theorem GroundTheory.Automorphic.HarishChandra.fischer_add_right (f g g' : MvPolynomial σ ℂ) :
    fischer f (g + g') = fischer f g + fischer f g' := by sorry
