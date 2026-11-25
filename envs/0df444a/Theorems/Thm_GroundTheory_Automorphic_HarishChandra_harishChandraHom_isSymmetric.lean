-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_harishChandraHom_isSymmetric
-- name    : GroundTheory.Automorphic.HarishChandra.harishChandraHom_isSymmetric
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:55:28.677885+00:00
-- url     : https://prove2.me/theorems/d2f4e456-6f8a-402b-a8ca-154b1cdf0a27
-- title:
--   Harish Chandra: harish Chandra Hom is Symmetric
-- statement:
--   The Harish Chandra construction uses the harish Chandra Hom is Symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L490-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L490-L508

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
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

theorem GroundTheory.Automorphic.HarishChandra.harishChandraHom_isSymmetric (z : Subalgebra.center ℂ (U n)) :
    (harishChandraHom z).IsSymmetric := by sorry
