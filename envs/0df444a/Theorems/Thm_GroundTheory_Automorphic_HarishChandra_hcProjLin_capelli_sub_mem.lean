-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_capelli_sub_mem
-- name    : GroundTheory.Automorphic.HarishChandra.hcProjLin_capelli_sub_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:55:22.518537+00:00
-- url     : https://prove2.me/theorems/dd9c948c-590b-42e8-8ddf-f2c1c7d838f8
-- title:
--   Harish Chandra: hc Proj Lin capelli sub mem
-- statement:
--   The Harish Chandra construction uses the hc Proj Lin capelli sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L158-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L158-L163

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

theorem GroundTheory.Automorphic.HarishChandra.hcProjLin_capelli_sub_mem (k : ℕ) :
    hcProjLin (capelli (n := n) (k + 1)) - psum (Fin n) ℂ (k + 1) ∈ polyLE n k := by sorry
