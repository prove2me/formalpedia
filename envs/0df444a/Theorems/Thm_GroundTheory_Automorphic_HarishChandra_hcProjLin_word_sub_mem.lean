-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_word_sub_mem
-- name    : GroundTheory.Automorphic.HarishChandra.hcProjLin_word_sub_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:15.806301+00:00
-- url     : https://prove2.me/theorems/53ac8d2c-1ab8-4b63-9b3e-b1110bf2e38b
-- title:
--   Harish Chandra: hc Proj Lin word sub mem
-- statement:
--   The Harish Chandra construction uses the hc Proj Lin word sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L82-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L82-L107

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

theorem GroundTheory.Automorphic.HarishChandra.hcProjLin_word_sub_mem (w : List (Fin n × Fin n)) :
    hcProjLin (word w) - diagMain w ∈ polyLE n (w.length - 1) := by sorry
