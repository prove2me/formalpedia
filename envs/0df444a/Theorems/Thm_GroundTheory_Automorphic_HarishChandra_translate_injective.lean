-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_injective
-- name    : GroundTheory.Automorphic.HarishChandra.translate_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:28.805891+00:00
-- url     : https://prove2.me/theorems/342fb880-5959-5ef1-b158-2bb53466e317
-- title:
--   Harish Chandra: translate injective
-- statement:
--   The Harish Chandra construction uses the translate injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Injective.lean#L68-L69

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

theorem GroundTheory.Automorphic.HarishChandra.translate_injective (c : Fin n → ℂ) : Function.Injective (translate (n := n) c) := by sorry
