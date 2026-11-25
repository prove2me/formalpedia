-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_totalDegree_harishChandraHom_capelli_sub
-- name    : GroundTheory.Automorphic.HarishChandra.totalDegree_harishChandraHom_capelli_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:11.144913+00:00
-- url     : https://prove2.me/theorems/6ce62d4c-8efa-516c-b3a1-9f7ee33fc3d7
-- title:
--   Harish Chandra: total Degree harish Chandra Hom capelli sub
-- statement:
--   The Harish Chandra construction uses the total Degree harish Chandra Hom capelli sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L250-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L250-L264

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_capelli_mem_center

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

theorem GroundTheory.Automorphic.HarishChandra.totalDegree_harishChandraHom_capelli_sub (k : ℕ) :
    (harishChandraHom (⟨capelli (k + 1), capelli_mem_center _⟩ : Subalgebra.center ℂ (U n)) -
      psum (Fin n) ℂ (k + 1)).totalDegree < k + 1 := by sorry
