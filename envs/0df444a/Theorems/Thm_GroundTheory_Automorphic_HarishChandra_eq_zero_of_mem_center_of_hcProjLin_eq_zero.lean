-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eq_zero_of_mem_center_of_hcProjLin_eq_zero
-- name    : GroundTheory.Automorphic.HarishChandra.eq_zero_of_mem_center_of_hcProjLin_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:50.418343+00:00
-- url     : https://prove2.me/theorems/cf047842-1d9f-4e73-b9c8-afb645843b86
-- title:
--   Harish Chandra: eq zero of mem center of hc Proj Lin eq zero
-- statement:
--   The Harish Chandra construction uses the eq zero of mem center of hc Proj Lin eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L38-L54

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Injective
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

theorem GroundTheory.Automorphic.HarishChandra.eq_zero_of_mem_center_of_hcProjLin_eq_zero {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (h : hcProjLin z = 0) : z = 0 := by sorry
