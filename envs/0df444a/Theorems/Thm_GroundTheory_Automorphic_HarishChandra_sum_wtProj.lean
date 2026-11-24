-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_wtProj
-- name    : GroundTheory.Automorphic.HarishChandra.sum_wtProj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:31:17.271445+00:00
-- url     : https://prove2.me/theorems/932cbcc4-ae7a-4c0b-9eff-a0768a64d76a
-- title:
--   Harish Chandra: sum wt Proj
-- statement:
--   The Harish Chandra construction uses the sum wt Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L173-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L173-L181

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

theorem GroundTheory.Automorphic.HarishChandra.sum_wtProj (f : Poly n) : ∑ ν ∈ f.support.image rowWt, wtProj ν f = f := by sorry
