-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_exists_adjoint
-- name    : GroundTheory.Automorphic.HarishChandra.exists_adjoint
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:48.253903+00:00
-- url     : https://prove2.me/theorems/ae2614f0-6234-474a-9347-5f871c24ecdd
-- title:
--   Harish Chandra: exists adjoint
-- statement:
--   The Harish Chandra construction uses the exists adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L13-L36

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

theorem GroundTheory.Automorphic.HarishChandra.exists_adjoint (u : U n) :
    ∃ u' : U n, ∀ f g : Poly n, fischer (rho 0 u f) g = fischer f (rho 0 u' g) := by sorry
