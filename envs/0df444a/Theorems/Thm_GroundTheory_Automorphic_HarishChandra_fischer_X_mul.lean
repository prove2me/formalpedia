-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_X_mul
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_X_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:38.704143+00:00
-- url     : https://prove2.me/theorems/4dd533dd-3973-43e6-a40c-e0a944cd7f50
-- title:
--   Harish Chandra: fischer X mul
-- statement:
--   The Harish Chandra construction uses the fischer X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L93-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L93-L128

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

theorem GroundTheory.Automorphic.HarishChandra.fischer_X_mul (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (X a * f) g = fischer f (pderiv a g) := by sorry
