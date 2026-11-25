-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_centralizerT_of_mem_center
-- name    : GroundTheory.Automorphic.HarishChandra.mem_centralizerT_of_mem_center
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:30.648072+00:00
-- url     : https://prove2.me/theorems/a72cf648-c028-432a-97fb-f6e96061b4b6
-- title:
--   Harish Chandra: mem centralizer T of mem center
-- statement:
--   The Harish Chandra construction uses the mem centralizer T of mem center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L318-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L318-L320

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

theorem GroundTheory.Automorphic.HarishChandra.mem_centralizerT_of_mem_center {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    z ∈ centralizerT n := by sorry
