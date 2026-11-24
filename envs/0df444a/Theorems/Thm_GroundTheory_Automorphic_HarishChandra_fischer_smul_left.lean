-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_smul_left
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_smul_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:45.015855+00:00
-- url     : https://prove2.me/theorems/4a5fa205-3bcd-4d27-a864-5ca6098a44d3
-- title:
--   Harish Chandra: fischer smul left
-- statement:
--   The Harish Chandra construction uses the fischer smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L40-L43

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

theorem GroundTheory.Automorphic.HarishChandra.fischer_smul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer (c • f) g = star c * fischer f g := by sorry
