-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_conjU_mem_center
-- name    : GroundTheory.Automorphic.HarishChandra.conjU_mem_center
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:47:13.815115+00:00
-- url     : https://prove2.me/theorems/fc56337a-c56b-51e0-8cf8-7663cc322df3
-- title:
--   Harish Chandra: conj U mem center
-- statement:
--   The Harish Chandra construction uses the conj U mem center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L54-L58

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Consequences
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

theorem GroundTheory.Automorphic.HarishChandra.conjU_mem_center {g : (gl n)ˣ} {z : U n} (hz : z ∈ Subalgebra.center ℂ (U n)) :
    conjU g z ∈ Subalgebra.center ℂ (U n) := by sorry
