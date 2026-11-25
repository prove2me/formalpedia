-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_eq_zero_of_mem_sup
-- name    : GroundTheory.Automorphic.HarishChandra.hcProjLin_eq_zero_of_mem_sup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:21.94115+00:00
-- url     : https://prove2.me/theorems/5f4d39e7-684e-4f5f-b8be-4794c0446ed2
-- title:
--   Harish Chandra: hc Proj Lin eq zero of mem sup
-- statement:
--   The Harish Chandra construction uses the hc Proj Lin eq zero of mem sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L90-L93

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
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

theorem GroundTheory.Automorphic.HarishChandra.hcProjLin_eq_zero_of_mem_sup {x : U n} (hx : x ∈ nMinusU n ⊔ nPlusU n) :
    hcProjLin x = 0 := by sorry
