-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_harishChandraHom_injective
-- name    : GroundTheory.Automorphic.HarishChandra.harishChandraHom_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:15.7503+00:00
-- url     : https://prove2.me/theorems/e315c2c7-5d97-4b57-907f-034ae5e4466c
-- title:
--   Harish Chandra: harish Chandra Hom injective
-- statement:
--   The Harish Chandra construction uses the harish Chandra Hom injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L71-L74

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

theorem GroundTheory.Automorphic.HarishChandra.harishChandraHom_injective : Function.Injective (harishChandraHom (n := n)) := by sorry
