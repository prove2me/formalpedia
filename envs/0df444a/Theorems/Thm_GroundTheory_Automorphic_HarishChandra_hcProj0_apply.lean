-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
-- name    : GroundTheory.Automorphic.HarishChandra.hcProj0_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:28.893539+00:00
-- url     : https://prove2.me/theorems/5636014b-f628-5b12-a0ab-99e80559e51a
-- title:
--   Harish Chandra: hc Proj0 apply
-- statement:
--   The Harish Chandra construction uses the hc Proj0 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L264-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L264-L264

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

theorem GroundTheory.Automorphic.HarishChandra.hcProj0_apply (z : centralizerT n) : hcProj0 z = hcProjLin (z : U n) := by sorry

attribute [defeq] GroundTheory.Automorphic.HarishChandra.hcProj0_apply
