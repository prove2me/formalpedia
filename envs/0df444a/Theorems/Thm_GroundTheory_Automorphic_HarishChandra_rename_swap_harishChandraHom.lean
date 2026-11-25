-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rename_swap_harishChandraHom
-- name    : GroundTheory.Automorphic.HarishChandra.rename_swap_harishChandraHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:21.48814+00:00
-- url     : https://prove2.me/theorems/1e255c0c-01b5-4bcc-8ebf-4bc94c6e8bf0
-- title:
--   Harish Chandra: rename swap harish Chandra Hom
-- statement:
--   The Harish Chandra construction uses the rename swap harish Chandra Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L462-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean#L462-L488

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

theorem GroundTheory.Automorphic.HarishChandra.rename_swap_harishChandraHom {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (z : Subalgebra.center ℂ (U n)) :
    rename (Equiv.swap i j) (harishChandraHom z) = harishChandraHom z := by sorry
