-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sub_hcEmb_mem
-- name    : GroundTheory.Automorphic.HarishChandra.sub_hcEmb_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:17.500123+00:00
-- url     : https://prove2.me/theorems/ae862221-c3af-4c55-9178-58f437d1e508
-- title:
--   Harish Chandra: sub hc Emb mem
-- statement:
--   The Harish Chandra construction uses the sub hc Emb mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L95-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L95-L110

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

theorem GroundTheory.Automorphic.HarishChandra.sub_hcEmb_mem (u : U n) : u - hcEmb (hcProjLin u) ∈ nMinusU n ⊔ nPlusU n := by sorry
