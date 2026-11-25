-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_eq_iff
-- name    : GroundTheory.Automorphic.HarishChandra.hcProjLin_eq_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:13.650046+00:00
-- url     : https://prove2.me/theorems/4683948a-b6ea-5550-9a77-aec4e7ff4c25
-- title:
--   Harish Chandra: hc Proj Lin eq iff
-- statement:
--   The Harish Chandra construction uses the hc Proj Lin eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L112-L118

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

theorem GroundTheory.Automorphic.HarishChandra.hcProjLin_eq_iff (u : U n) (p : MvPolynomial (Fin n) ℂ) :
    hcProjLin u = p ↔ u - hcEmb p ∈ nMinusU n ⊔ nPlusU n := by sorry
