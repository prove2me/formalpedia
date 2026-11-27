-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_totalDegree_hcProjLin_capelli_sub
-- name    : GroundTheory.Automorphic.HarishChandra.totalDegree_hcProjLin_capelli_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:53:46.436861+00:00
-- url     : https://prove2.me/theorems/0aa5e2c8-35e7-5dde-908b-5c1eb344e220
-- title:
--   Harish Chandra: total Degree hc Proj Lin capelli sub
-- statement:
--   The Harish Chandra construction uses the total Degree hc Proj Lin capelli sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L165-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L165-L167

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.totalDegree_hcProjLin_capelli_sub (k : ℕ) :
    (hcProjLin (capelli (n := n) (k + 1)) - psum (Fin n) ℂ (k + 1)).totalDegree < k + 1 := by sorry
