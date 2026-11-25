-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_neg_translate
-- name    : GroundTheory.Automorphic.HarishChandra.translate_neg_translate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:05.394902+00:00
-- url     : https://prove2.me/theorems/342cb755-22a9-4c96-9743-67b7d5776694
-- title:
--   Harish Chandra: translate neg translate
-- statement:
--   The Harish Chandra construction uses the translate neg translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L63-L66

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

theorem GroundTheory.Automorphic.HarishChandra.translate_neg_translate (c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    translate (-c) (translate c p) = p := by sorry
