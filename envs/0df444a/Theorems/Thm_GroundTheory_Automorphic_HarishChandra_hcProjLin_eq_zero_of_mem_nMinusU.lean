-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_eq_zero_of_mem_nMinusU
-- name    : GroundTheory.Automorphic.HarishChandra.hcProjLin_eq_zero_of_mem_nMinusU
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:59.348161+00:00
-- url     : https://prove2.me/theorems/6b7db150-4283-4d80-a724-7dc9528ca8be
-- title:
--   Harish Chandra: hc Proj Lin eq zero of mem n Minus U
-- statement:
--   The Harish Chandra construction uses the hc Proj Lin eq zero of mem n Minus U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L78-L88

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

theorem GroundTheory.Automorphic.HarishChandra.hcProjLin_eq_zero_of_mem_nMinusU {x : U n} (hx : x ∈ nMinusU n) : hcProjLin x = 0 := by sorry
