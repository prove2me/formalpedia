-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_harishChandraHom_apply
-- name    : GroundTheory.Automorphic.HarishChandra.harishChandraHom_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:42.081453+00:00
-- url     : https://prove2.me/theorems/dbfd41c3-234f-5358-9cba-f20ef92437e9
-- title:
--   Harish Chandra: harish Chandra Hom apply
-- statement:
--   The Harish Chandra construction uses the harish Chandra Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L311-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L311-L312

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

theorem GroundTheory.Automorphic.HarishChandra.harishChandraHom_apply (z : Subalgebra.center ℂ (U n)) :
    harishChandraHom z = translate (-rhoVec n) (hcProjLin (z : U n)) := by sorry
