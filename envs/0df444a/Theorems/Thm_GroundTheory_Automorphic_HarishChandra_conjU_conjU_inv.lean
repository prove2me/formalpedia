-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_conjU_conjU_inv
-- name    : GroundTheory.Automorphic.HarishChandra.conjU_conjU_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:24.089731+00:00
-- url     : https://prove2.me/theorems/ee3ea030-fa4f-48ee-ab90-4d2a543122f7
-- title:
--   Harish Chandra: conj U conj U inv
-- statement:
--   The Harish Chandra construction uses the conj U conj U inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L44-L52

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

theorem GroundTheory.Automorphic.HarishChandra.conjU_conjU_inv (g : (gl n)ˣ) (u : U n) : conjU g (conjU g⁻¹ u) = u := by sorry
