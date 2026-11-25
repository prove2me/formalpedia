-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_self
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_self
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:55.848688+00:00
-- url     : https://prove2.me/theorems/66f1e214-64cc-405b-8e3c-e2951c7cd425
-- title:
--   Harish Chandra: fischer self
-- statement:
--   The Harish Chandra construction uses the fischer self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L134-L139

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

theorem GroundTheory.Automorphic.HarishChandra.fischer_self (f : MvPolynomial σ ℂ) :
    fischer f f = ((∑ m ∈ f.support, (mfact m : ℝ) * Complex.normSq (coeff m f) : ℝ) : ℂ) := by sorry
