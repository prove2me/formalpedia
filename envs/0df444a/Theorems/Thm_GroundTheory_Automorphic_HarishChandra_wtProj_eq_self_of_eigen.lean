-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_eq_self_of_eigen
-- name    : GroundTheory.Automorphic.HarishChandra.wtProj_eq_self_of_eigen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:01.98136+00:00
-- url     : https://prove2.me/theorems/bfdd8882-cec7-4710-9da7-13482199e553
-- title:
--   Harish Chandra: wt Proj eq self of eigen
-- statement:
--   The Harish Chandra construction uses the wt Proj eq self of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L166-L171

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

theorem GroundTheory.Automorphic.HarishChandra.wtProj_eq_self_of_eigen {h : Poly n} (ν : Fin n → ℕ)
    (hc : ∀ a, rowOp a a h = (ν a : ℂ) • h) : wtProj ν h = h := by sorry
