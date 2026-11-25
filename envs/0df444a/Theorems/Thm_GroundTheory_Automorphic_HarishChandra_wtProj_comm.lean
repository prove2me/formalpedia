-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_comm
-- name    : GroundTheory.Automorphic.HarishChandra.wtProj_comm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:13.596789+00:00
-- url     : https://prove2.me/theorems/39ef67b9-f37a-40e6-ae70-3dc70d028c37
-- title:
--   Harish Chandra: wt Proj comm
-- statement:
--   The Harish Chandra construction uses the wt Proj comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L197-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L197-L218

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
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
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.wtProj_comm {T : Module.End ℂ (Poly n)} (hT : ∀ a, T * rowOp a a = rowOp a a * T)
    (μ : Fin n → ℕ) (f : Poly n) : wtProj μ (T f) = T (wtProj μ f) := by sorry
