-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_injOn_center
-- name    : GroundTheory.Automorphic.HarishChandra.hcProjLin_injOn_center
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:10.146516+00:00
-- url     : https://prove2.me/theorems/84da5726-77c6-50ad-a326-18ce5c4b5401
-- title:
--   Harish Chandra: hc Proj Lin inj On center
-- statement:
--   The Harish Chandra construction uses the hc Proj Lin inj On center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L56-L61

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

theorem GroundTheory.Automorphic.HarishChandra.hcProjLin_injOn_center :
    Set.InjOn (hcProjLin (n := n)) (Subalgebra.center ℂ (U n) : Set (U n)) := by sorry
