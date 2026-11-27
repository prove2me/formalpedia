-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_totalDegree_hcProjLin_le
-- name    : GroundTheory.Automorphic.HarishChandra.totalDegree_hcProjLin_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:53:39.350128+00:00
-- url     : https://prove2.me/theorems/27194199-1def-547f-a1b3-cf9bb720bb6b
-- title:
--   Harish Chandra: total Degree hc Proj Lin le
-- statement:
--   The Harish Chandra construction uses the total Degree hc Proj Lin le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L48-L50

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

theorem GroundTheory.Automorphic.HarishChandra.totalDegree_hcProjLin_le {d : ℕ} {u : U n} (hu : u ∈ filt d) :
    (hcProjLin u).totalDegree ≤ d := by sorry
