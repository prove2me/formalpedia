-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_wtProj
-- name    : GroundTheory.Automorphic.HarishChandra.wtProj_wtProj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:57.729691+00:00
-- url     : https://prove2.me/theorems/18b3147a-3a6d-41c7-88a6-9bf1d5f4e29a
-- title:
--   Harish Chandra: wt Proj wt Proj
-- statement:
--   The Harish Chandra construction uses the wt Proj wt Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L142-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L142-L156

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

theorem GroundTheory.Automorphic.HarishChandra.wtProj_wtProj (μ ν : Fin n → ℕ) (f : Poly n) :
    wtProj μ (wtProj ν f) = if μ = ν then wtProj ν f else 0 := by sorry
