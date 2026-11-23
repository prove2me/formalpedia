-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_add_left
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:41.461573+00:00
-- url     : https://prove2.me/theorems/9cb1fc3d-bd24-427f-a799-5b308b0e6329
-- title:
--   Harish Chandra: fischer add left
-- statement:
--   The Harish Chandra construction uses the fischer add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L36-L38

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

theorem GroundTheory.Automorphic.HarishChandra.fischer_add_left (f f' g : MvPolynomial σ ℂ) :
    fischer (f + f') g = fischer f g + fischer f' g := by sorry
