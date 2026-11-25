-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mfact_pos
-- name    : GroundTheory.Automorphic.HarishChandra.mfact_pos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:07.434449+00:00
-- url     : https://prove2.me/theorems/2904b17c-686d-45fa-9608-b38aa7e37d2e
-- title:
--   Harish Chandra: mfact pos
-- statement:
--   The Harish Chandra construction uses the mfact pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L11-L12

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

theorem GroundTheory.Automorphic.HarishChandra.mfact_pos (m : σ →₀ ℕ) : 0 < mfact m := by sorry
