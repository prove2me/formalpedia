-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_eq_self_iff
-- name    : GroundTheory.Automorphic.HarishChandra.wtProj_eq_self_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:57.227404+00:00
-- url     : https://prove2.me/theorems/e35325d7-f135-4781-bf43-e6c56109dc29
-- title:
--   Harish Chandra: wt Proj eq self iff
-- statement:
--   The Harish Chandra construction uses the wt Proj eq self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L126-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L126-L140

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

theorem GroundTheory.Automorphic.HarishChandra.wtProj_eq_self_iff (μ : Fin n → ℕ) (f : Poly n) :
    wtProj μ f = f ↔ ∀ m ∈ f.support, rowWt m = μ := by sorry
